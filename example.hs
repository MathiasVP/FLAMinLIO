{-# LANGUAGE PostfixOperators #-}
module Example where

import Lib.FLAM
import Lib.LIO
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad.State

withClearance :: Principal -> (BoundedLabel FLAM, H, Strategy Principal)
withClearance p = (BoundedLabel { _cur = bot, _clearance = p }, H Set.empty, [])

runExample = evalStateT (unLIO (runFLAM example)) $ withClearance top

example :: FLAMIO ()
example = do
  withStrategy [bot] $ do
    addDelegate ("alice", "bob") bot
    newScope $ do
      removeDelegate ("alice", "bob") bot
      b <- "alice" ≽ "bob"
      liftLIO $ LIO $ lift $ print b
    b <- "alice" ≽ "bob"
    liftLIO $ LIO $ lift $ print b
