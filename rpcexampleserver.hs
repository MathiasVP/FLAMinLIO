{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module RPCExampleServer where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.List as List
import Control.Lens
import qualified Data.ByteString.Char8 as B8
import Data.Dynamic.Binary
import qualified Data.Binary as Bin
import qualified Data.ByteString.Lazy as BL   

example :: FLAMIO ()
example = do
  export "f" (exportable2 (replicate :: Int -> String -> [String]))
  serveRPC ("127.0.0.1", "8000", "Client") $ \socket -> do
    recvRPC socket >>= \case
      Just (s, args) -> do
        lookupRPC s >>= \case
          Just g -> do
            case invoke g args of
              Just r -> sendRPCResult socket (Just r)
          Nothing -> error "Lookup failed!"
      Nothing -> error "Receive failed!"

main :: IO ()
main =
  evalStateT (runFLAM example)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
