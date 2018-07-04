{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module ForwardExampleNode1 where

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
  addDelegate ("Alice" ←) ("Bob" ←) bot
  withStrategy [bot] $ do
    addDelegate "Alice" "Bob" bot
  serveRPC ("127.0.0.1", "8000", "Server") $ \socket -> do
    liftFLAMIO $ liftLIO $ liftIO $ threadDelay 1000000
    return ()

main :: IO ()
main =
  evalStateT (runFLAM example)
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
