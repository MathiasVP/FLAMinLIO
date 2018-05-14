{-# LANGUAGE LambdaCase, PostfixOperators, MonadComprehensions, ExplicitForAll, ScopedTypeVariables, FlexibleContexts #-}
module FLAMinLIO where
import FLAM
import LIO
import Control.Monad.State
import qualified Data.Set as Set
import Data.Set(Set)

withClearance :: Principal -> (BoundedLabel FLAM, H, Strategy Principal)
withClearance p = (BoundedLabel { _cur = bot, _clearance = p }, H Set.empty, [])

example :: FLAMIO Bool
example = do
  ab <- label bot (("a" %), ("b" %))
  setState ([H $ Set.fromList [ab]])
  ("b" →) ⊑ ("a" →)

example_trans :: FLAMIO Bool
example_trans = do
  ab <- label bot (("a" %), ("b" %))
  bc <- label bot ((%) "b", (%) "c")
  setState ([H $ Set.fromList [ab, bc]])
  ("c" →) ⊑ ("a" →)

example_raise :: FLAMIO Bool
example_raise = do
  pq <- label top (("p" %), ("q" %))
  setState ([H $ Set.fromList [pq]])
  ("q" →) ⊑ ("p" →)

example2 :: FLAMIO Bool
example2 = do
  pq <- label top (("p" %), ("q" %))
  setState ([H $ Set.fromList [pq]])
  ("p" →) ≽ ("q" →)

example3 :: FLAMIO Bool
example3 = ((:→) (:⊤) :/\ (:←) (:⊤)) ≽ ((:→) (:⊤) :/\ (:←) (:⊥))

example4 :: FLAMIO Bool
example4 = do
  pq <- label top (("p" %), ("q" %))
  setState ([H $ Set.fromList [pq]])
  ((:⊤) →) :/\ ((:⊤) ←) ≽ (((:⊤) →) :/\ ((:⊥) ←))

-- Bad use of setState can leak!
example_implicit_bad :: Labeled FLAM Bool -> FLAMIO Bool
example_implicit_bad secret = do
  _ <- toLabeled top $ do
    lab <- label bot (("alice" %), ("bob" %))
    s <- unlabel secret
    when s $ do
      setState ([H $ Set.fromList [lab]])
  (%) "alice" ≽ (%) "bob"

example_implicit2_bad :: FLAMIO Bool
example_implicit2_bad = do
  strategy [bot] $ do
    s <- label top False
    example_implicit_bad s

-- We can fix this by using the addDelegate function instead.
example_implicit :: Labeled FLAM Bool -> FLAMIO Bool
example_implicit secret = do
  _ <- toLabeled top $ do
    s <- unlabel secret
    when s $ do
      addDelegate (("alice" %), ("bob" %)) bot
  (%) "alice" ≽ (%) "bob"

example_implicit2 :: FLAMIO Bool
example_implicit2 = do
  strategy [bot] $ do
    s <- label top True
    example_implicit s

{- The following example demonstrates how an attacker can add a "bad" delegation
   to circumvent the IFC -}
attack :: FLAMIO ()
attack = do
  top_trusts_bot <- label bot ((:⊥), (:⊤))
  setState ([H $ Set.singleton top_trusts_bot])

use_attack :: Labeled FLAM Bool -> FLAMIO Bool
use_attack x = do
  attack -- When this line is commented out there is a IFC error (as expected)
         -- But when the attack is present the code is unlabeled with no errors
  unlabel x

-- Run the example with clearance = bot
example_attack :: FLAMIO Bool
example_attack = do
  -- Pretend we have a secret boolean coming in from somewhere
  use_attack (Labeled { _labeledLab = top, _labeledVal = True })

example5 :: FLAMIO Bool
example5 = (((:→) (:⊥)) :/\ ((:←) (:⊤))) ⊑ (((:→) (:⊤)) :/\ ((:←) (:⊥)))
