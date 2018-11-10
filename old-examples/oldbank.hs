{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE LambdaCase, PostfixOperators, GeneralizedNewtypeDeriving #-}

module Main where
import Lib.FLAM
import Lib.LIO
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

instance MonadFLAMIO (BankT FLAMIO) where
  liftFLAMIO = lift
  
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
      when (balance >= amount) $ do
        from -= amount
        to += amount
    Nothing -> return ()

getBalance :: Customer -> BankT FLAMIO Balance
getBalance u =
  gets (Map.lookup u) >>= \case
    Just account -> lift $ unlabel account
    Nothing -> return 0

addRole :: String -> BankT FLAMIO ()
addRole role = lift $ addDelegate ("Bank", role) bot

addCustomer :: String -> BankT FLAMIO ()
addCustomer customer =
  lift $ addDelegate ("Bank" .: customer, "Customer") bot

createAccount :: String -> BankT FLAMIO ()
createAccount customer = do
  account <- lift $ label (customer %) 100
  modify $ Map.insert customer account

addAccountManager :: String -> BankT FLAMIO ()
addAccountManager accountant =
  lift $ addDelegate ("Bank" .: accountant, "Manager") bot

addDirector :: String -> BankT FLAMIO ()
addDirector dir = do
  lift $ addDelegate ("Bank" .: dir, "Director") bot

assignAccountManager :: String -> String -> BankT FLAMIO () 
assignAccountManager manager customer = do
  let ℓ = (((manager \/ customer) →) \/ ((manager /\ customer) ←))
  lift $ addDelegate ((manager →), (customer →)) ℓ
  lift $ addDelegate ((customer ←), (manager ←)) ℓ

asUser :: User -> BankT FLAMIO () -> BankT FLAMIO ()
asUser u m = do
  toLabeled_ (u %) m
  return ()

runBank :: BankT FLAMIO a -> FLAMIO (a, Bank)
runBank = flip runStateT Map.empty . unBankT

evalBank :: BankT FLAMIO a -> FLAMIO a
evalBank = flip evalStateT Map.empty . unBankT

execBank :: BankT FLAMIO a -> FLAMIO Bank
execBank = flip execStateT Map.empty . unBankT

example :: FLAMIO Bank
example = execBank $ do
  withStrategy noStrategy $ do
    addRole "Customer"  
    addRole "Manager"
    addRole "Director"

    addCustomer "Charlie"
    addCustomer "Chloe"
    addCustomer "Charlotte"
    
    createAccount "Charlie"
    
    createAccount "Chloe"
    createAccount "Charlotte"

    addAccountManager "Matt"
    addAccountManager "Michael"
  
    addDirector "David"
  
    assignAccountManager "Matt" "Charlie"
    assignAccountManager "Michael" "Chloe"
    assignAccountManager "Michael" "Charlotte"

  -- Matt is Charlie's account manager, so he can see the amount of money on Charlie's account
  withStrategy (Strategy ["Matt"]) $ do
    asUser "Matt" $ do
      Map.lookup "Charlie" <$> get >>= \case
        Just amount -> do
          a <- unlabel amount
          {- ... -}
          return ()
        Nothing -> return ()

  -- Chloe is allowed to wire money from her own account to Charlotte
  {-asUser "Chloe" $ do
    transfer "Chloe" "Charlotte" 10

  
  
  -- Michael is the manager of Chloe's account, so he can move money from Chloe to Charlie
  withStrategy ["Michael"] $ do
    asUser "Michael" $ do
      transfer "Chloe" "Charlie" 20-}

{-
  -- Charlie asks Chloe to take out 10 dollars from his account and give it to Charlotte
  -- So Charlie temporarily gives authority to Chloe
  newScope $ do
    withStrategy [bot] $ do
      asUser "Charlie" $ addDelegate ("Chloe", "Charlie") bot
      asUser "Chloe" $ transfer "Charlie" "Charlotte" 10
  
  -- Charlie is not allowed to transfer money from Charlotte to his own account!
  -- Thows IFC error, as required.
  {-strategy [] $ do
    asUser "Charlie" $ do
      transfer "Charlotte" "Charlie" 30-} -}
runExample :: IO Bank
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)

main :: IO ()
main = runExample >>= print
