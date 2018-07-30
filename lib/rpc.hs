{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Lib.RPC where

import Lib.LIO
import Lib.FLAM
import Lib.Network
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Catch
import qualified Data.List as List
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net
import Control.Lens.Tuple
import Data.Typeable
import Data.Binary
import Data.Dynamic.Binary
import Control.Lens hiding ((:<))

instance {-# Overlaps #-} (MonadFLAMIO m, Binary a) => RPCInvokable (m a)
instance {-# Overlaps #-} (Binary a, RPCInvokable r) => RPCInvokable (a -> r)

class RPCType a where
  rpc :: (Binary b, Typeable b, Show b, Bin.Binary b) => LSocketRPC -> String -> b -> a

class RPCType' a where
  rpc' :: (Binary b, Typeable b, Show b, Bin.Binary b) => LSocketRPC -> [Dynamic] -> String -> b -> a

instance RPCType' a => RPCType a where
  rpc socket f args = rpc' socket [] f args

instance (Typeable a, Binary a, RPCType' r, Show a, Bin.Binary a) => RPCType' (a -> r) where
  rpc' socket args f arg1 = \arg2 -> rpc' socket (toDyn arg1 : args) f arg2

instance (Binary a, Typeable a, Bin.Binary a) => RPCType' (FLAMIO (Maybe a)) where
  rpc' (LSocketRPC (s, name)) args f arg = do
    liftIO $ Net.send s (BL.toStrict $ encode (f, List.reverse (toDyn arg : args)))
    liftIO (Net.recv s 1024) >>= \case
      Just bs -> do
        case (decodeOrFail (BL.fromStrict bs)) of
          Left _ -> return Nothing
          Right (_, _, Just a) -> return $ fromDynamic a
          _ -> return Nothing
      Nothing -> return Nothing

recvRPC :: forall m a . (MonadIO m, MonadMask m, MonadFLAMIO m) => LSocketRPC -> m (Maybe (String, [Dynamic]))
recvRPC (LSocketRPC (s, name)) = do
  Net.recv s 1024 >>= \case
    Nothing -> return Nothing
    Just bs -> do
      case decodeOrFail (BL.fromStrict bs) of
        Left _ -> return Nothing
        Right (_, _, y) -> return $ Just y

invoke :: (MonadFLAMIO m, Typeable m) => RPCInvokableExt -> [Dynamic] -> m (Maybe Dynamic)
invoke (RPCInvokableExt f) xs = c f xs

sendRPCResult :: (MonadIO m, MonadMask m, MonadFLAMIO m, Binary a) => LSocketRPC -> Maybe a -> m ()
sendRPCResult (LSocketRPC (s, name)) ma = Net.send s (BL.toStrict $ encode ma)

instance (Typeable a) => Curryable' 'False a where
  c' _ a [] = do
    case cast a of
      Just ma -> ma
      Nothing -> return Nothing

instance (Typeable a, Typeable b, Curryable b) => Curryable' 'True (a -> b) where
  c' _ f (x : xs) = do
    case (cast x :: Maybe a) of
      Just a -> c (f a) xs
      _ -> return Nothing

exportable1 :: (MonadFLAMIO m, Bin.Binary a, Bin.Binary b, Typeable a, Typeable b) => (a -> m b) -> Dynamic -> m (Maybe Dynamic)
exportable1 f da = do
  case fromDynamic da of
    Just a -> Just . toDyn <$> f a
    Nothing -> return Nothing

exportable2 :: (MonadFLAMIO m, Bin.Binary a, Bin.Binary b, Bin.Binary c, Typeable a, Typeable b, Typeable c) => (a -> b -> m c) -> Dynamic -> Dynamic -> m (Maybe Dynamic)
exportable2 f da db = do
  case (fromDynamic da, fromDynamic db) of
    (Just a, Just b) -> Just . toDyn <$> f a b
    _ -> return Nothing

exportable3 :: (MonadFLAMIO m, Bin.Binary a, Bin.Binary b, Bin.Binary c, Bin.Binary d, Typeable a, Typeable b, Typeable c, Typeable d) => (a -> b -> c -> m d) -> Dynamic -> Dynamic -> Dynamic -> m (Maybe Dynamic)
exportable3 f da db dc = do
  case (fromDynamic da, fromDynamic db, fromDynamic dc) of
    (Just a, Just b, Just c) -> Just . toDyn <$> f a b c
    _ -> return Nothing
