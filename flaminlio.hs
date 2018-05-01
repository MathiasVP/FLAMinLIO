{-# LANGUAGE LambdaCase, PostfixOperators, MonadComprehensions, ExplicitForAll, ScopedTypeVariables, FlexibleContexts #-}
module FLAMinLIO where
import FLAM
import LIO
import qualified Data.Set.Monad as Set
import Data.Set.Monad(Set)
import Control.Monad.State

withClearance :: Principal -> (BoundedLabel FLAM, H, Strategy Principal)
withClearance p = (BoundedLabel { _cur = bot, _clearance = p }, H Set.empty, [])

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
example_implicit secret = do
  _ <- toLabeled top $ do
    s <- unlabel secret
    when s $ do
      addDelegate (("alice" %), ("bob" %)) bot
  (%) "alice" ≽ (%) "bob"

example_implicit2 :: LIO H FLAM Bool
example_implicit2 = do
  setStrategy [bot]
  s <- label top False
  example_implicit s

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
