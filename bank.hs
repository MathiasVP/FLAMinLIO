{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE LambdaCase, PostfixOperators, GeneralizedNewtypeDeriving #-}

module Bank where
import FLAM
import LIO
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.State
import Control.Lens hiding ((+=), (-=))

type Customer = String
type User = String
type Amount = Int
type Balance = Int
type Bank = Map Customer (Labeled Principal Balance)

newtype BankT m a = BankT { unBankT :: StateT Bank m a }
  deriving (Functor, Applicative, Monad, MonadState Bank, MonadTrans)

instance HasCache (Cache Principal) (BankT FLAMIO) where
  getCache = BankT getCache
  putCache = BankT . putCache

instance (Label s l, MonadLIO s l m) => MonadLIO s l (BankT m) where
  liftLIO = BankT . liftLIO
  
(+=) :: Customer -> Amount -> BankT FLAMIO ()
(+=) user amount =
  gets (Map.lookup user) >>= \case
  Just Labeled{ _labeledLab = lab, _labeledVal = balance } ->
    modify (Map.insert user Labeled { _labeledLab = lab, _labeledVal = balance + amount })
  Nothing -> return ()

(-=) :: Customer -> Amount -> BankT FLAMIO ()
u -= amount = u += (- amount)

transfer :: Customer -> Customer -> Amount -> BankT FLAMIO ()
transfer from to amount =
  gets (Map.lookup from) >>= \case
    Just account -> do
      balance <- lift $ unlabel account
      if balance >= amount then do
        from -= amount
        to += amount
      else return ()
    Nothing -> return ()

getBalance :: Customer -> BankT FLAMIO Balance
getBalance u =
  gets (Map.lookup u) >>= \case
    Just account -> lift $ unlabel account
    Nothing -> return 0

{-
addRole :: String -> BankT FLAMIO ()
addRole role = lift $ addDelegate (("Bank" %), (role %)) bot
-}

addCustomer :: String -> BankT FLAMIO ()
addCustomer customer =
  lift $ addDelegate ((customer %), ("Customer" %)) bot

createAccount :: String -> BankT FLAMIO ()
createAccount customer = do
  account <- lift $ label (customer %) 100
  modify $ Map.insert customer account

addAccountManager :: String -> BankT FLAMIO ()
addAccountManager accountant =
  lift $ addDelegate ((accountant %), ("Manager" %)) bot

addDirector :: String -> BankT FLAMIO ()
addDirector dir = do
  lift $ addDelegate ((dir %), ("Director" %)) (("Bank" ←) \/ ((:⊥) →))

assignAccountManager :: String -> String -> BankT FLAMIO () 
assignAccountManager manager customer = do
  lift $ addDelegate ((manager →), (customer →)) (manager \/ customer)
  lift $ addDelegate ((customer ←), (manager ←)) (manager \/ customer)

asUser :: User -> BankT FLAMIO () -> BankT FLAMIO ()
asUser u m = do
  l <- getLabel
  clr <- getClearance
  liftLIO $ modify $ _1 . clearance .~ (u %)
  _ <- m
  liftLIO $ modify $ _1 . cur .~ l
  liftLIO $ modify $ _1 . clearance .~ clr

runBank :: BankT FLAMIO a -> FLAMIO (a, Bank)
runBank = flip runStateT Map.empty . unBankT

evalBank :: BankT FLAMIO a -> FLAMIO a
evalBank = flip evalStateT Map.empty . unBankT

execBank :: BankT FLAMIO a -> FLAMIO Bank
execBank = flip execStateT Map.empty . unBankT

lhs :: Principal
lhs = (:→) ((Name "Charlotte" :\/ Name "Michael") :/\ (Name "Chloe" :\/ Name "Michael")) :/\ (:←) (:⊤)

rhs :: Principal
rhs = Name "Michael"

lhs' :: Principal
lhs' = ((rhs →) /\ (lhs ←))

rhs' :: Principal
rhs' = ((lhs →) /\ (rhs ←))

-- (:→) (Name "Michael") :/\ (:←) (:⊤) ≽ (:→) ((Name "Charlotte" :\/ Name "Michael") :/\ (Name "Chloe" :\/ Name "Michael")) :/\ (:←) (Name "Michael")

example :: FLAMIO Bank
example = execBank $ do
  lift $ setStrategy []
  addCustomer "Chloe"
  addCustomer "Charlotte"
  addAccountManager "Michael"
  assignAccountManager "Michael" "Chloe"
  assignAccountManager "Michael" "Charlotte"
  liftLIO $ LIO $ lift $ putStrLn "————————————————————————"
  -- Michael is the manager of Chloe's account, so he can move money from
  -- Chloe to Charlie
  lift $ setStrategy [("Michael" %)]
  asUser "Michael" $ do
    b <- (:→) ((Name "Charlotte" :\/ Name "Michael") :/\ (Name "Chloe" :\/ Name "Michael")) :/\ (:←) (:⊤) ⊑ Name "Michael"
    liftLIO $ LIO $ lift $ putStrLn (show b)
    return ()

runExample :: IO Bank
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
