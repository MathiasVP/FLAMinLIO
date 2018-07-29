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

instance {-# Overlaps #-} Binary a => RPCInvokable a
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

invoke :: RPCInvokableExt -> [Dynamic] -> Maybe Dynamic
invoke (RPCInvokableExt f) = join . c f

sendRPCResult :: (MonadIO m, MonadMask m, MonadFLAMIO m, Binary a) => LSocketRPC -> Maybe a -> m ()
sendRPCResult (LSocketRPC (s, name)) ma = Net.send s (BL.toStrict $ encode ma)

instance Typeable a => Curryable' 'False a where
  c' _ a [] = cast a

instance (Typeable a, Typeable b, Curryable b) => Curryable' 'True (a -> b) where
  c' _ f (x : xs) =
    case (cast x :: Maybe a) of
      Just a -> c (f a) xs
      _ -> Nothing

exportable1 :: (Bin.Binary a, Bin.Binary b, Typeable a, Typeable b) => (a -> b) -> Dynamic -> Maybe Dynamic
exportable1 f da = do
  a <- fromDynamic da
  return $ toDyn $ f a

exportable2 :: (Bin.Binary a, Bin.Binary b, Bin.Binary c, Typeable a, Typeable b, Typeable c) => (a -> b -> c) -> Dynamic -> Dynamic -> Maybe Dynamic
exportable2 f da db = do
  a <- fromDynamic da
  b <- fromDynamic db
  return $ toDyn $ f a b

exportable3 :: (Bin.Binary a, Bin.Binary b, Bin.Binary c, Bin.Binary d, Typeable a, Typeable b, Typeable c, Typeable d) => (a -> b -> c -> d) -> Dynamic -> Dynamic -> Dynamic -> Maybe Dynamic
exportable3 f da db dc = do
  a <- fromDynamic da
  b <- fromDynamic db
  c <- fromDynamic dc
  return $ toDyn $ f a b c
