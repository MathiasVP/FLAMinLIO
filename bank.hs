{-# LANGUAGE LambdaCase, PostfixOperators #-}

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

(+=) :: Customer -> Amount -> StateT Bank FLAMIO ()
(+=) user amount =
  gets (Map.lookup user) >>= \case
  Just Labeled{ _labeledLab = lab, _labeledVal = balance } ->
    modify (Map.insert user Labeled { _labeledLab = lab, _labeledVal = balance + amount })
  Nothing -> return ()

(-=) :: Customer -> Amount -> StateT Bank FLAMIO ()
u -= amount = u += (- amount)

transfer :: Customer -> Customer -> Amount -> StateT Bank FLAMIO ()
transfer from to amount =
  gets (Map.lookup from) >>= \case
    Just account -> do
      balance <- lift $ unlabel account
      if balance >= amount then do
        from -= amount
        to += amount
      else return ()
    Nothing -> return ()

getBalance :: Customer -> StateT Bank FLAMIO Balance
getBalance u =
  gets (Map.lookup u) >>= \case
    Just account -> lift $ unlabel account
    Nothing -> return 0

addRole :: String -> StateT Bank FLAMIO ()
addRole role = lift $ addDelegate (("Bank" %), (role %)) bot

addCustomer :: String -> StateT Bank FLAMIO ()
addCustomer customer =
  lift $ addDelegate ("Bank" .: customer, ("Customer" %)) ((("Manager" \/ customer) ←) /\ ((:⊥) →))

createAccount :: String -> StateT Bank FLAMIO ()
createAccount customer = do
  account <- lift $ label (customer %) 100
  modify $ Map.insert customer account

addAccountManager :: String -> StateT Bank FLAMIO ()
addAccountManager accountant =
  lift $ addDelegate ("Bank" .: accountant, ("Manager" %)) ((accountant ←) /\ ((:⊥) →))

addDirector :: String -> StateT Bank FLAMIO ()
addDirector dir = do
  lift $ addDelegate ("Bank" .: dir, ("Director" %)) (("Bank" ←) \/ ((:⊥) →))

assignAccountManager :: String -> String -> StateT Bank FLAMIO () 
assignAccountManager manager customer = do
  lift $ addDelegate ((manager →), (customer →)) (manager \/ customer)
  lift $ addDelegate ((customer ←), (manager ←)) (manager \/ customer)

asUser :: User -> StateT Bank FLAMIO () -> StateT Bank FLAMIO ()
asUser u m = do
  l <- getLabel
  clr <- getClearance
  lift $ lift $ LIO $ modify $ (_1 . clearance .~ (u %))
  _ <- m
  lift $ lift $ LIO $ modify $ (_1 . cur .~ l)
  lift $ lift $ LIO $ modify $ (_1 . clearance .~ clr)

runBank :: StateT Bank FLAMIO a -> FLAMIO (a, Bank)
runBank = flip runStateT Map.empty

evalBank :: StateT Bank FLAMIO a -> FLAMIO a
evalBank = flip evalStateT Map.empty

execBank :: StateT Bank FLAMIO a -> FLAMIO Bank
execBank = flip execStateT Map.empty

example :: FLAMIO Bank
example = execBank $ do
  lift $ setStrategy []
  
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
  lift $ setStrategy [("Matt" %)]
  asUser "Matt" $ do
    Map.lookup "Charlie" <$> get >>= \case
      Just amount -> do
        liftLIO $ LIO $ lift $ putStrLn "Computing Charlie ⊑ Matt"
        b1 <- lift $ ("Charlie" %) ⊑ ("Matt" %)
        liftLIO $ LIO $ lift $ putStrLn $ "Done: " ++ show b1
        liftLIO $ LIO $ lift $ putStrLn "Recomputing Charlie ⊑ Matt"
        b2 <- lift $ ("Charlie" %) ⊑ ("Matt" %)
        liftLIO $ LIO $ lift $ putStrLn $ "Done: " ++ show b2
        a <- lift $ unlabel amount
        {- ... -}
        return ()
      Nothing -> return ()
  
  -- Chloe is allowed to wire money from her own account to Charlotte
  lift $ setStrategy []
  asUser "Chloe" $ do
    transfer "Chloe" "Charlotte" 10

  lift $ setStrategy [("Michael" %)]
  -- Michael is the manager of Chloe's account, so he can move money from Chloe to Charlie
  asUser "Michael" $ do
    transfer "Chloe" "Charlie" 20
    
  -- Charlie is not allowed to transfer money from Charlotte to his own account!
  {-lift $ setStrategy []
  asUser "Charlie" $ do
    transfer "Charlotte" "Charlie" 30-}

runExample :: IO Bank
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
