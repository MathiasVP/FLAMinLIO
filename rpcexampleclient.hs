{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module RPCExampleClient where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import Control.Lens

example :: FLAMIO ()
example = do
  connectRPC ("127.0.0.1", "8000", "Server") $ \socket -> do
    rpc socket "f" (10 :: Int) ("a" :: String) >>= \case
      Just (p :: [String]) -> liftIO $ print p
      Nothing -> error "RPC failed!"
    return ()

main :: IO ()
main =
  evalStateT (runFLAM example)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
