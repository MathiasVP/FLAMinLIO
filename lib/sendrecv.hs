{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PostfixOperators #-}
module Lib.SendRecv where

import Control.Monad.IO.Class
import Data.Binary
import qualified Data.ByteString.Lazy as BL
import qualified Network.Simple.TCP as Net
import Data.Typeable

import GHC.Generics

send :: (MonadIO m, Binary a, Show a) => Net.Socket -> a -> m ()
send socket a =
  let d = encode a
  in do
    --liftIO $ putStrLn $ "Sending: " ++ show a ++ " on socket: " ++ show socket
    --liftIO $ putStrLn $ "Bytes are: " ++ show (BL.append (encode (fromIntegral (BL.length d) :: Int)) d)
    Net.sendLazy socket (BL.append (encode (fromIntegral (BL.length d) :: Int)) d)

recv :: forall m a . (MonadIO m, Binary a, Show a, Typeable a) => Net.Socket -> m (Maybe a)
recv socket = do
  Net.recv socket 8 >>= \case
    Just bs -> do
      --liftIO $ putStrLn $ "Received length: " ++ show bs ++ " on socket: " ++ show socket
      case decodeOrFail (BL.fromStrict bs) of
        Left _ -> return Nothing
        Right (_, _, len :: Int) -> do
          Net.recv socket len >>= \case
            Just bs' -> do
              --liftIO $ putStrLn $ "Received data: " ++ show bs' ++ " on socket: " ++ show socket
              case decodeOrFail (BL.fromStrict bs') of
                          Left _ -> do
                            --liftIO $ putStrLn $ "Failed to decode as: " ++ show (typeRep (Proxy :: Proxy (Maybe a)))
                            return Nothing
                          Right (_, _, ma) -> do
                            --liftIO $ putStrLn $ "Decoded to: " ++ show ma
                            return $ Just ma
            Nothing -> return Nothing
    Nothing -> return Nothing
