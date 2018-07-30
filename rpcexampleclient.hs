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
import Bank
import Data.Dynamic.Binary
import Data.Binary

example :: FLAMIO ()
example = do
  connectRPC ("127.0.0.1", "8000", "Server") $ \socket -> do
    rpc socket "create" ("Mathias" :: User) >>= \case
      Just (p :: Response) -> liftIO $ print p
      Nothing -> error "RPC failed!"

    rpc socket "open" ("Mathias" :: User) ("Savings" :: Account) >>= \case
      Just (p :: Response) -> liftIO $ print p
      Nothing -> error "RPC failed!"
      
    rpc socket "getBalance" ("Mathias" :: User) ("Savings" :: Account) >>= \case
      Just (p :: Response) -> liftIO $ print p
      Nothing -> error "RPC failed!"

main :: IO ()
main =
  evalStateT (runFLAM example)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
