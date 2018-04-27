{-# LANGUAGE LambdaCase, PostfixOperators, MonadComprehensions, ExplicitForAll, ScopedTypeVariables, FlexibleContexts #-}
module FLAMinLIO where
import FLAM
import LIO
import qualified Data.Set.Monad as Set
import Data.Set.Monad(Set)
import Control.Monad.State

withClearance :: Principal -> (BoundedLabel FLAM, H)
withClearance p = (BoundedLabel { _cur = bot, _clearance = p }, H Set.empty)

example :: LIO H FLAM Bool
example = do
  ab <- label bot (("a" %), ("b" %))
  setState (H $ Set.fromList [ab])
  ("b" →) ⊑ ("a" →)

example_trans :: LIO H FLAM Bool
example_trans = do
  ab <- label bot (("a" %), ("b" %))
  bc <- label bot ((%) "b", (%) "c")
  setState (H $ Set.fromList [ab, bc])
  ("c" →) ⊑ ("a" →)

example_raise :: LIO H FLAM Bool
example_raise = do
  pq <- label top (("p" %), ("q" %))
  setState (H $ Set.fromList [pq])
  ("q" →) ⊑ ("p" →)

example2 :: LIO H FLAM Bool
example2 = do
  pq <- label top (("p" %), ("q" %))
  setState (H $ Set.fromList [pq])
  ("p" →) ≽ ("q" →)

example3 :: LIO H FLAM Bool
example3 = ((:→) (:⊤) :/\ (:←) (:⊤)) ≽ ((:→) (:⊤) :/\ (:←) (:⊥))

example4 :: LIO H FLAM Bool
example4 = do
  pq <- label top (("p" %), ("q" %))
  setState (H $ Set.fromList [pq])
  ((:⊤) →) :/\ ((:⊤) ←) ≽ (((:⊤) →) :/\ ((:⊥) ←))

example_implicit :: Labeled FLAM Bool -> LIO H FLAM Bool
example_implicit x = do
  b <- unlabel x
  when b $ do
    h <- getState
    d <- label (labelOf x) (("alice" %), ("bob" %))
    setState $ H (Set.insert d (unH h))
  (%) "alice" ≽ (%) "bob"

example_implicit2 :: LIO H FLAM Bool
example_implicit2 = do
  s <- label ("alice" \/ "bob") True
  example_implicit s

leak :: Labeled FLAM Int -> LIO H FLAM ()
leak secret = do
  _ <- toLabeled top $ do
    s <- unlabel secret
    when (s == 0) $ do
      del <- label top ((%) "alice", (%) "bob")
      setState $ H $ Set.singleton del
  {- IMPORTANT: The toLabeled function does a ⊑ to check if the current level of the
                computation above ``stayed below'' top, and this ⊑ actually raises the
                current level differently depending on whether s is zero or not:
                When s is zero a delegation is added, and the ⊑ computation raises the
                current level to bot ⊔ top = :⊤ doing this computation since it tries
                to use this new delegation.
                When s is non-zero no new delegation is added, and thus checking the ⊑
                keeps the current level at bot. -}
  l <- getLabel
  LIO . StateT $ \s -> do
    print l
    return ((), s)
  return ()

leak2 :: LIO H FLAM Bool
leak2 = do
  secret <- label top 1
  leak secret
  l <- getLabel
  (l →) ⊑ ((:⊥) →)

{- The following example demonstrates how an attacker can add a "bad" delegation
   to circumvent the IFC -}
attack :: LIO H FLAM ()
attack = do
  top_trusts_bot <- label bot ((:⊥), (:⊤))
  h <- getState
  setState (H $ Set.insert top_trusts_bot (unH h))

use_attack :: Labeled FLAM Bool -> LIO H FLAM Bool
use_attack x = do
  attack -- When this line is commented out there is a IFC error (as expected)
         -- But when the attack is present the code is unlabeled with no errors
  unlabel x

-- Run the example with clearance = bot
example_attack :: LIO H FLAM Bool
example_attack = do
  -- Pretend we have a secret boolean coming in from somewhere
  use_attack (Labeled { _labeledLab = top, _labeledVal = True })

example5 :: FLAMIO Bool
example5 = (((:→) (:⊥)) :/\ ((:←) (:⊤))) ⊑ (((:→) (:⊤)) :/\ ((:←) (:⊥)))
