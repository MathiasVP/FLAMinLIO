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
addRole role = addDelegate (("Bank" %), (role %)) bot

addCustomer :: String -> StateT Bank FLAMIO ()
addCustomer customer =
  addDelegate ("Bank" .: customer, ("Customer" %)) ((("Manager" \/ customer) ←) /\ ((:⊥) →))

createAccount :: String -> StateT Bank FLAMIO ()
createAccount customer = do
  account <- label (customer %) 100
  modify $ Map.insert customer account

addAccountManager :: String -> StateT Bank FLAMIO ()
addAccountManager accountant =
  addDelegate ("Bank" .: accountant, ("Manager" %)) ((accountant ←) /\ ((:⊥) →))

addDirector :: String -> StateT Bank FLAMIO ()
addDirector dir = do
  addDelegate ("Bank" .: dir, ("Director" %)) (("Bank" ←) \/ ((:⊥) →))

assignAccountManager :: String -> String -> StateT Bank FLAMIO () 
assignAccountManager manager customer = do
  addDelegate ((manager →), (customer →)) (manager \/ customer)
  addDelegate ((customer ←), (manager ←)) (manager \/ customer)

asUser :: User -> StateT Bank FLAMIO () -> StateT Bank FLAMIO ()
asUser u m = do
  l <- getLabel
  clr <- getClearance
  lift $ LIO $ modify $ (_1 . clearance .~ (u %))
  _ <- m
  lift $ LIO $ modify $ (_1 . cur .~ l)
  lift $ LIO $ modify $ (_1 . clearance .~ clr)

runBank :: StateT Bank FLAMIO a -> FLAMIO (a, Bank)
runBank = flip runStateT Map.empty

evalBank :: StateT Bank FLAMIO a -> FLAMIO a
evalBank = flip evalStateT Map.empty

execBank :: StateT Bank FLAMIO a -> FLAMIO Bank
execBank = flip execStateT Map.empty

example :: FLAMIO Bank
example = execBank $ do
  liftLIO $ setStrategy []
  
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

  -- Matt is Charlie's account manager, so he can see the amount
  -- of money on Charlie's account
  liftLIO $ setStrategy [("Matt" %)]
  asUser "Matt" $ do
    Map.lookup "Charlie" <$> get >>= \case
      Just amount -> do
        liftLIO $ LIO $ lift $ putStrLn "Computing Charlie ⊑ Matt"
        b1 <- ("Charlie" %) ⊑ ("Matt" %)
        liftLIO $ LIO $ lift $ print b1
        
        liftLIO $ LIO $ lift $ putStrLn "Recomputing Charlie ⊑ Matt"
        b2 <- ("Charlie" %) ⊑ ("Matt" %)
        liftLIO $ LIO $ lift $ print b2
        a <- unlabel amount
        {- ... -}
        return ()
      Nothing -> return ()
  
  -- Chloe is allowed to wire money from her own account to Charlotte
  liftLIO $ setStrategy []
  asUser "Chloe" $ do
    transfer "Chloe" "Charlotte" 10

  -- Michael is the manager of Chloe's account, so he can move money
  -- from Chloe to Charlie
  liftLIO $ setStrategy [("Michael" %)]
  asUser "Michael" $ do
    transfer "Chloe" "Charlie" 20
    
  -- Charlie is not allowed to transfer money from Charlotte to his own account!
  {-liftLIO $ setStrategy []
  asUser "Charlie" $ do
    transfer "Charlotte" "Charlie" 30-}

runExample :: IO Bank
runExample =
  evalStateT (unLIO example)
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
