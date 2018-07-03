{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE GADTs #-}
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
import Control.Lens hiding ((:<))

instance RPCInvokable Char
instance RPCInvokable a => RPCInvokable [a]
instance RPCInvokable Int
instance RPCInvokable ()
instance (Serializable a, RPCInvokable r) => RPCInvokable (a -> r)

class RPCType a where
  rpc :: (Serializable b, Typeable b, Show b) => LSocketRPC -> String -> b -> a

instance (Typeable a, Serializable a, RPCType r, Show a) => RPCType (a -> r) where
  rpc socket f arg1 = \arg2 -> rpc socket f (arg1, arg2)

instance Serializable a => RPCType (FLAMIO (Maybe a)) where
  rpc (LSocketRPC (s, name)) f args = do
    liftIO $ Net.send s (encode (f, args))
    liftIO (Net.recv s (maxSize (undefined :: Maybe a))) >>= \case
      Just bs -> do
        case (decode bs :: Maybe (Maybe a)) of
          Just a -> return a
          Nothing -> error "ROFL" --return Nothing
      Nothing -> return Nothing

recvRPC :: forall m a b . (MonadIO m, MonadMask m, MonadFLAMIO m, Serializable b) => LSocketRPC -> m (Maybe (String, b))
recvRPC (LSocketRPC (s, name)) =
  Net.recv s (maxSize (undefined :: (String, b))) >>= \case
    Nothing -> return Nothing
    Just x -> do
      case decode x of
        Nothing -> return Nothing
        Just y -> return $ Just y

sendRPCResult :: (MonadIO m, MonadMask m, MonadFLAMIO m, Serializable a) => LSocketRPC -> Maybe a -> m ()
sendRPCResult (LSocketRPC (s, name)) ma = Net.send s (encode ma) 

invoke :: (Typeable a, Typeable b) => RPCInvokableExt -> a -> Maybe b
invoke (RPCInvokableExt f) xs =
  case cast f of
    Just g -> Just $ g xs
    Nothing -> Nothing
