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
import Lib.SendRecv
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Catch
import qualified Data.List as List
import qualified Data.ByteString.Lazy as BL
import qualified Network.Simple.TCP as Net
import Control.Lens.Tuple
import Data.Typeable
import Data.Dynamic.Binary
import Control.Concurrent
import Data.Binary

instance {-# Overlaps #-} (MonadFLAMIO m, Binary a) => RPCInvokable (m a)
instance {-# Overlaps #-} (Binary a, RPCInvokable r) => RPCInvokable (a -> r)

class RPCType a where
  rpc :: (Binary b, Typeable b) => LSocketRPC -> String -> b -> a

class RPCType' a where
  rpc' :: (Binary b, Typeable b) => LSocketRPC -> [Dynamic] -> String -> b -> a
  
instance RPCType' a => RPCType a where
  rpc socket f args = rpc' socket [] f args

instance (Typeable a, Binary a, RPCType' r) => RPCType' (a -> r) where
  rpc' socket args f arg1 = \arg2 -> rpc' socket (toDyn arg1 : args) f arg2

instance (Binary a, Typeable a) => RPCType' (FLAMIO (Maybe a)) where
  rpc' (LSocketRPC (s, name)) args f arg = do
    liftIO $ send s (Just (f, List.reverse (toDyn arg : args)))
    liftIO (recv s) >>= \case
      Just (lma :: Labeled Principal (Maybe Dynamic)) -> do
        ma <- unlabel lma
        case ma of
          Just a -> return $ fromDynamic a
          Nothing -> return Nothing
      Nothing -> return Nothing

recvRPC :: forall m a . (MonadIO m, MonadMask m, MonadFLAMIO m) => LSocketRPC -> m (Maybe (Maybe (String, [Dynamic])))
recvRPC (LSocketRPC (s, name)) = recv s

invoke :: (MonadFLAMIO m, Typeable m) => RPCInvokableExt -> [Dynamic] -> m (Maybe Dynamic)
invoke (RPCInvokableExt f) xs = c f xs

sendRPCResult :: (MonadIO m, MonadMask m, MonadFLAMIO m, Binary a, Show a) => LSocketRPC -> Maybe a -> m ()
sendRPCResult (LSocketRPC (s, name)) ma = do
  cur <- getLabel
  lma <- label cur ma
  send s lma

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

exportable1 :: (MonadFLAMIO m, Binary a, Binary b, Typeable a, Typeable b) => (a -> m b) -> Dynamic -> m (Maybe Dynamic)
exportable1 f da = do
  case fromDynamic da of
    Just a -> Just . toDyn <$> f a
    Nothing -> return Nothing

exportable2 :: (MonadFLAMIO m, Binary a, Binary b, Binary c, Typeable a, Typeable b, Typeable c) => (a -> b -> m c) -> Dynamic -> Dynamic -> m (Maybe Dynamic)
exportable2 f da db = do
  case (fromDynamic da, fromDynamic db) of
    (Just a, Just b) -> Just . toDyn <$> f a b
    _ -> return Nothing

exportable3 :: (MonadFLAMIO m, Binary a, Binary b, Binary c, Binary d, Typeable a, Typeable b, Typeable c, Typeable d) => (a -> b -> c -> m d) -> Dynamic -> Dynamic -> Dynamic -> m (Maybe Dynamic)
exportable3 f da db dc = do
  case (fromDynamic da, fromDynamic db, fromDynamic dc) of
    (Just a, Just b, Just c) -> Just . toDyn <$> f a b c
    _ -> return Nothing

exportable4 :: (MonadFLAMIO m, Binary a, Binary b, Binary c, Binary d, Binary e, Typeable a, Typeable b, Typeable c, Typeable d, Typeable e) => (a -> b -> c -> d -> m e) -> Dynamic -> Dynamic -> Dynamic -> Dynamic -> m (Maybe Dynamic)
exportable4 f da db dc dd = do
  case (fromDynamic da, fromDynamic db, fromDynamic dc, fromDynamic dd) of
    (Just a, Just b, Just c, Just d) -> Just . toDyn <$> f a b c d
    _ -> return Nothing

exportable5 :: (MonadFLAMIO m, Binary a, Binary b, Binary c, Binary d, Binary e, Binary g, Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable g) => (a -> b -> c -> d -> e -> m g) -> Dynamic -> Dynamic -> Dynamic -> Dynamic -> Dynamic -> m (Maybe Dynamic)
exportable5 f da db dc dd dg = do
  case (fromDynamic da, fromDynamic db, fromDynamic dc, fromDynamic dd, fromDynamic dg) of
    (Just a, Just b, Just c, Just d, Just g) -> Just . toDyn <$> f a b c d g
    _ -> return Nothing
