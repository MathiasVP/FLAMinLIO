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
import qualified Data.Map as Map
import Control.Lens
import Bank
import Data.Typeable
import Data.Dynamic.Binary

getBalance :: User -> Account -> BankT FLAMIO Response
getBalance u a =
  Map.lookup u <$> get >>= \case
    Just lacc ->
      Map.lookup a <$> unlabel lacc >>= \case
        Just bal -> do
          liftIO $ putStrLn $ "Sending balance " ++ show bal
          return $ Balance bal
        Nothing -> do
          liftIO $ putStrLn $ "Sending NoSuchAccount"
          return $ NoSuchAccount
    Nothing -> do
      liftIO $ putStrLn $ "Sending NoSuchUser"
      return $ NoSuchUser

example :: BankT FLAMIO ()
example = do
  export "getBalance" (exportable2 getBalance)
  serveRPC ("127.0.0.1", "8000", "Client") $ \socket -> do
    liftIO $ putStrLn "Waiting for rpc..."
    recvRPC socket >>= \case
      Just (s, args) -> do
        lookupRPC s >>= \case
          Just g -> do
            invoke g args >>= \case
              Just r -> sendRPCResult socket (Just r)
              Nothing -> error "Invoke failed!"
          Nothing -> error "Lookup failed!"
      Nothing -> error "Receive failed!"

main :: IO ()
main =
  evalStateT (runFLAM $ evalStateT (runBankT example) Map.empty)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
