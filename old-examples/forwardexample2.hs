{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module ForwardExampleNode2 where

import System.IO
import Lib.FLAM
import Lib.LIO
import Lib.RPC
import Lib.Network
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.State
import Control.Concurrent

example :: FLAMIO ()
example = do
  connectRPC ("127.0.0.1", "8000", (⊤)) $ \socket -> do
    withStrategy [bot] $ do
      x <- "Alice" ≽ "Bob"
      liftFLAMIO $ liftLIO $ liftIO $ print x
    return ()

main :: IO ()
main =
  evalStateT (runFLAM example)
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
