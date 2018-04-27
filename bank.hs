{-# LANGUAGE LambdaCase, PostfixOperators #-}

module Bank where
import FLAM
import LIO
import qualified Data.Set.Monad as Set
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.State

type User = String
type Amount = Int
type Balance = Int
type Bank = Map User (Labeled Principal Amount)

(+=) :: User -> Amount -> StateT Bank FLAMIO ()
(+=) user amount =
  gets (Map.lookup user) >>= \case
  Just account -> do
    balance <- lift $ unlabel account
    newBalance <- lift $ label (user %) (balance + amount)
    modify (Map.insert user newBalance)
  Nothing -> do
    newBalance <- lift $ label (user %) amount
    modify (Map.insert user newBalance)

(-=) :: User -> Amount -> StateT Bank FLAMIO ()
u -= amount = u += (- amount)

transfer :: Principal -> User -> User -> Amount -> StateT Bank FLAMIO ()
transfer accountant from to amount =
  lift ((accountant %) ≽ (from %)) >>= \case
    True -> do
      gets (Map.lookup from) >>= \case
        Just account -> do
          balance <- lift $ unlabel account
          if balance >= amount then do
            from -= amount
            to += amount
          else return ()
        Nothing -> return ()
    False -> return ()

getBalance :: User -> StateT Bank FLAMIO Balance
getBalance u =
  gets (Map.lookup u) >>= \case
    Just account -> lift $ unlabel account
    Nothing -> return 0

addRole :: String -> StateT Bank FLAMIO ()
addRole role = do
  h <- lift $ getState
  del <- lift $ label bot (("Bank" %), (role %))
  lift $ setState $ H $ Set.insert del (unH h)

addCustomer :: String -> StateT Bank FLAMIO ()
addCustomer customer = do
  h <- lift $ getState
  del <- lift $ label ((("Manager" \/ customer) ←) /\ ((:⊥) →))
    ("Bank" .: customer, ("Customer" %))
  lift $ setState $ H $ Set.insert del (unH h)

addAccountManager :: String -> StateT Bank FLAMIO ()
addAccountManager accountant = do
  h <- lift $ getState
  del <- lift $ label ((("Director" \/ accountant) ←) /\ ((:⊥) →))
    ("Bank" .: accountant, ("Manager" %))
  lift $ setState $ H $ Set.insert del (unH h)

addDirector :: String -> StateT Bank FLAMIO ()
addDirector dir = do
  h <- lift $ getState
  del <- lift $ label (("Bank" ←) \/ ((:⊥) →))
    ("Bank" .: dir, ("Director" %))
  lift $ setState $ H $ Set.insert del (unH h)

assignAccountManager :: String -> String -> StateT Bank FLAMIO () 
assignAccountManager manager customer = do
  h <- lift $ getState
  del <- lift $ label (manager \/ customer) ((manager %), (customer %))
  lift $ setState $ H $ Set.insert del (unH h)

evalBank :: StateT Bank FLAMIO a -> FLAMIO a
evalBank = flip evalStateT Map.empty

example :: FLAMIO Bool
example = evalBank $ do
  lift $ liftLIO $ setStrategy []
  
  addRole "Customer"  
  addRole "Manager"
  addRole "Director"

  addCustomer "Charlie"
  addCustomer "Chloe"
  addCustomer "Charlotte"

  addAccountManager "Matt"
  addAccountManager "Michael"
  
  addDirector "David"
  
  assignAccountManager "Matt" "Charlie"
  assignAccountManager "Michael" "Chloe"
  assignAccountManager "Michael" "Charlotte"

  lift $ liftLIO $ setStrategy [("Matt" %)]
  b <- ("Charlie" →) ⊑ ("Matt" →)

  l <- lift $ liftLIO $ getLabel

  lift $ liftLIO $ LIO . StateT $ \st -> do
    print l
    return ((), st)
  return b

runExample :: IO Bool
runExample =
  evalStateT (unLIO example)
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
