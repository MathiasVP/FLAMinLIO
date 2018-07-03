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
import Data.Tuple.Only
import qualified Data.ByteString.Char8 as B8

f :: Int -> String -> String
f n1 s = List.concat $ replicate n1 s

g :: Principal -> Principal -> Principal
g p1 p2 = p1 ⊔ p2

example :: FLAMIO ()
example = do
  export "f" f
  export "g" g
  serveRPC ("127.0.0.1", "8000", "Client") $ \socket -> do
    recvRPC socket >>= \case
      Just (s, args :: (Principal, Principal)) ->
        lookupRPC s >>= \case
          Just f -> do
            case invoke f args of
              Just (a :: Principal) -> sendRPCResult socket (Just a)
              Nothing -> do
                error "Invoke failed!"
                sendRPCResult socket (Nothing :: Maybe Int)
          Nothing -> error "Lookup failed!"
      Nothing -> error "Receive failed!"

main :: IO ()
main =
  evalStateT (runFLAM example)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
