{-# LANGUAGE PostfixOperators #-}
module Example where

import FLAM
import LIO
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad.State

withClearance :: Principal -> (BoundedLabel FLAM, [H], Strategy Principal)
withClearance p = (BoundedLabel { _cur = bot, _clearance = p }, [H Set.empty], [])

bobSecret :: Labeled FLAM Int
bobSecret = Labeled { _labeledLab = bot, _labeledVal = 42 }

runExample = evalStateT (unLIO (runFLAM example)) $ withClearance top

{-
runExample = evalStateT (unLIO (runFLAM example)) $ withClearance ("alice" %)

example :: FLAMIO Bool
example = do
  liftLIO $ setState $ H (Set.fromList [Labeled { _labeledVal = (("bob" ←), ("alice" ←)), _labeledLab = ("charlie" %) },
                                        Labeled { _labeledVal = (("alice" →), ("bob" →)), _labeledLab = ("charlie" %) }])
  setStrategy [("bob" %)]
  b <- ("bob" %) ⊑ ("alice" %)
  return b
-}

{-
example :: FLAMIO ()
example = do
  strategy [bot] $ do
    scope $ do
      addDelegate (("alice" %), ("bob" %)) bot
      b <- "alice" ≽ "bob"
      liftLIO $ LIO $ lift $ print b
    b <- "alice" ≽ "bob"
    liftLIO $ LIO $ lift $ print b
-}

{- QUESTION: Is this behavior what we intent? -}

example :: FLAMIO ()
example = do
  strategy [bot] $ do
    addDelegate (("alice" %), ("bob" %)) bot
    scope $ do
      -- alice can still act for bob from the outer scope. Is this what we want?
      removeDelegate (("alice" %), ("bob" %)) bot
      b <- "alice" ≽ "bob"
      liftLIO $ LIO $ lift $ print b
    b <- "alice" ≽ "bob"
    liftLIO $ LIO $ lift $ print b
