{-# LANGUAGE LambdaCase, PostfixOperators, MonadComprehensions, ExplicitForAll, ScopedTypeVariables, FlexibleContexts #-}
module FLAMinLIO where
import FLAM
import LIO
import qualified Data.Set.Monad as Set
import Data.Set.Monad(Set)
import Control.Monad.State

{-
emptyH :: (Label l, Ord l) => l -> LIO l (H l) 
emptyH l = H <$> newRef l Set.empty

insert :: (Label l, Ord l) => H l -> l -> (Principal, Principal) -> LIO l ()
insert (H h) l (p, q) = do
  h' <- (!) $ h
  del <- label l (p, q)
  h .= Set.insert del h'

delete :: (Label l, Ord l) => H l -> l -> (Principal, Principal) -> LIO l ()
delete (H h) l (p, q) = do
  h' <- (!) $ h
  del <- label l (p, q)
  h .= Set.delete del h'
-}

example :: LIO H FLAM Bool
example = do
  ab <- label bot ((%) "a", (%) "b")
  setState (H $ Set.fromList [ab])
  ("b" →) ⊑ ("a" →)

example_trans :: LIO H FLAM Bool
example_trans = do
  ab <- label bot ((%) "a", (%) "b")
  bc <- label bot ((%) "b", (%) "c")
  setState (H $ Set.fromList [ab, bc])
  ("c" →) ⊑ ("a" →)

example_raise :: LIO H FLAM Bool
example_raise = do
  pq <- label top ((%) "p", (%) "q")
  setState (H $ Set.fromList [pq])
  ("q" →) ⊑ ("p" →)

example2 :: LIO H FLAM Bool
example2 = do
  setState (H $ Set.fromList [Labeled { _labeledLab = top,
                                        _labeledVal = (Name "p", Name "q") }])
  ("p" →) ≽ ("q" →)

example3 :: LIO H FLAM Bool
example3 = ((:→) (:⊤) :/\ (:←) (:⊤)) ≽ ((:→) (:⊤) :/\ (:←) (:⊥))

example4 :: LIO H FLAM Bool
example4 = do
  setState (H $ Set.fromList [Labeled { _labeledLab = top,
                                        _labeledVal = (Name "p", Name "q") }])
  ((:⊤) →) :/\ ((:⊤) ←) ≽ (((:⊤) →) :/\ ((:⊥) ←))

example_implicit :: Labeled FLAM Bool -> LIO H FLAM Bool
example_implicit x = do
  b <- unlabel x
  when b $ do
    h <- getState
    d <- label (labelOf x) ((%) "alice", (%) "bob")
    setState $ H (Set.insert d (unH h))
  (%) "alice" ≽ (%) "bob"

example_implicit2 :: LIO H FLAM Bool
example_implicit2 = do
  s <- label ("alice" \|/ "bob") True
  example_implicit s
