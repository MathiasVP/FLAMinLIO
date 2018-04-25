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

addAccountant :: Principal -> User -> StateT Bank FLAMIO ()
addAccountant accountant user = do
  h <- lift $ getState
  del <- lift $ label (accountant :\/ (user %)) (accountant, (user %))
  lift $ setState $ H $ Set.insert del (unH h)

initialBank :: Bank
initialBank = Map.fromList []

initialH :: H
initialH = H $ Set.fromList [Labeled { _labeledLab = bot,
                                       _labeledVal = (("bob" →), ("alice" →))}]

evalBank :: StateT Bank FLAMIO a -> FLAMIO a
evalBank = flip evalStateT initialBank

example :: FLAMIO Amount
example = evalBank $ do
  "alice" += 100
  _ <- toLabeled ("alice" %) $ do
    addAccountant ("John Doe" %) "alice"
    transfer ("John Doe" %) "alice" "bob" 25
  b <- getBalance "bob"
  l <- lift $ getLabel
  lift $ LIO . StateT $ \s -> do
    print l
    return ((), s)
  return b
