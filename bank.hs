{-# LANGUAGE LambdaCase, PostfixOperators #-}

module Bank where
import FLAM
import LIO
import qualified Data.Set.Monad as Set
import Data.Set.Monad(Set)
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad
import Data.Maybe

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
          {- At this point the current label is alice->.
             That is, we have observed sensitive information to Alice, which we now
             transfer to Bob. For this to work we need to ensure that Bob's
             confidentiality can act for Alice's confidentiality. -}
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
  del <- lift $ label (("Bank" .: "Manager") ←) ((customer %), "Bank" .: "Customer")
  lift $ setState $ H $ Set.insert del (unH h)

addAccountManager :: String -> StateT Bank FLAMIO ()
addAccountManager accountant = do
  h <- lift $ getState
  del <- lift $ label (("Bank" .: "Director") ←) ((accountant %), "Bank" .: "Manager")
  lift $ setState $ H $ Set.insert del (unH h)

addDirector :: String -> StateT Bank FLAMIO ()
addDirector dir = do
  h <- lift $ getState
  del <- lift $ label ("Bank" ←) ((dir %), "Bank" .: "Director")
  lift $ setState $ H $ Set.insert del (unH h)

assignAccountManager :: String -> String -> StateT Bank FLAMIO () 
assignAccountManager manager customer = do
  h <- lift $ getState
  del <- lift $ label bot ((manager %), (customer %))
  lift $ setState $ H $ Set.insert del (unH h)

evalBank :: StateT Bank FLAMIO a -> FLAMIO a
evalBank = flip evalStateT Map.empty

example :: FLAMIO Amount
example = evalBank $ do
  -- Initial bank
  "alice" += 100

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

  b <- liftLIO $ ("Charlie" →) ⊑ ("David" →)
  lift $ LIO . StateT $ \s -> do
    print b
    return ((), s)
  return 0
