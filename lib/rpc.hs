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
import Lib.Serializable
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
import Data.Tuple.Only
import Control.Lens hiding ((:<))

instance {-# Overlaps #-} Serializable a => RPCInvokable a
instance {-# Overlaps #-} (Serializable a, RPCInvokable r) => RPCInvokable (a -> r)

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
          Nothing -> return Nothing
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
invoke (RPCInvokableExt f) xs = c f xs

instance {-# Overlaps #-} (Typeable a, Typeable b) => Curryable (a -> b) where
  c f x =
    case (cast f, cast x :: Maybe a) of
      (Just g, Just a) -> Just $ g a
      _ -> Nothing

instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c) => Curryable (a -> b -> c) where
  c f x =
    case (cast f, cast x :: Maybe (a, b)) of
      (Just g, Just (a, b)) -> Just $ g a b
      _ -> case (cast f, cast x :: Maybe a) of
             (Just g, Just a) -> Just $ g a
             _ -> Nothing
      
instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c, Typeable d) => Curryable (a -> b -> c -> d) where
  c f x =
    case (cast f, cast x :: Maybe ((a, b), c)) of
      (Just g, Just ((a, b), c)) -> Just $ g a b c
      _ -> case (cast f, cast x :: Maybe (a, b)) of
             (Just g, Just (a, b)) -> Just $ g a b
             _ -> case (cast f, cast x :: Maybe a) of
                    (Just g, Just a) -> Just $ g a
                    _ -> Nothing

instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e) => Curryable (a -> b -> c -> d -> e) where
  c f x =
    case (cast f, cast x :: Maybe (((a, b), c), d)) of
      (Just g, Just (((a, b), c), d)) -> Just $ g a b c d
      _ ->
        case (cast f, cast x :: Maybe ((a, b), c)) of
          (Just g, Just ((a, b), c)) -> Just $ g a b c
          _ ->
            case (cast f, cast x :: Maybe (a, b)) of
              (Just g, Just (a, b)) -> Just $ g a b
              _ ->
                case (cast f, cast x :: Maybe a) of
                  (Just g, Just a) -> Just $ g a
                  _ -> Nothing

instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable h) => Curryable (a -> b -> c -> d -> e -> h) where
  c f x =
    case (cast f, cast x :: Maybe ((((a, b), c), d), e)) of
      (Just g, Just ((((a, b), c), d), e)) -> Just $ g a b c d e
      _ ->
        case (cast f, cast x :: Maybe (((a, b), c), d)) of
          (Just g, Just (((a, b), c), d)) -> Just $ g a b c d
          _ ->
            case (cast f, cast x :: Maybe ((a, b), c)) of
              (Just g, Just ((a, b), c)) -> Just $ g a b c
              _ ->
                case (cast f, cast x :: Maybe (a, b)) of
                  (Just g, Just (a, b)) -> Just $ g a b
                  _ ->
                    case (cast f, cast x :: Maybe a) of
                      (Just g, Just a) -> Just $ g a
                      _ -> Nothing

instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable h, Typeable i) => Curryable (a -> b -> c -> d -> e -> h -> i) where
  c f x =
    case (cast f, cast x :: Maybe (((((a, b), c), d), e), h)) of
      (Just g, Just (((((a, b), c), d), e), h)) -> Just $ g a b c d e h
      _ ->
        case (cast f, cast x :: Maybe ((((a, b), c), d), e)) of
          (Just g, Just ((((a, b), c), d), e)) -> Just $ g a b c d e
          _ ->
            case (cast f, cast x :: Maybe (((a, b), c), d)) of
              (Just g, Just (((a, b), c), d)) -> Just $ g a b c d
              _ ->
                case (cast f, cast x :: Maybe ((a, b), c)) of
                  (Just g, Just ((a, b), c)) -> Just $ g a b c
                  _ ->
                    case (cast f, cast x :: Maybe (a, b)) of
                      (Just g, Just (a, b)) -> Just $ g a b
                      _ ->
                        case (cast f, cast x :: Maybe a) of
                          (Just g, Just a) -> Just $ g a
                          _ -> Nothing

instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable h, Typeable i, Typeable j) => Curryable (a -> b -> c -> d -> e -> h -> i -> j) where
  c f x =
    case (cast f, cast x :: Maybe ((((((a, b), c), d), e), h), i)) of
      (Just g, Just ((((((a, b), c), d), e), h), i)) -> Just $ g a b c d e h i
      _ ->
        case (cast f, cast x :: Maybe (((((a, b), c), d), e), h)) of
          (Just g, Just (((((a, b), c), d), e), h)) -> Just $ g a b c d e h
          _ ->
            case (cast f, cast x :: Maybe ((((a, b), c), d), e)) of
              (Just g, Just ((((a, b), c), d), e)) -> Just $ g a b c d e
              _ ->
                case (cast f, cast x :: Maybe (((a, b), c), d)) of
                  (Just g, Just (((a, b), c), d)) -> Just $ g a b c d
                  _ ->
                    case (cast f, cast x :: Maybe ((a, b), c)) of
                      (Just g, Just ((a, b), c)) -> Just $ g a b c
                      _ ->
                        case (cast f, cast x :: Maybe (a, b)) of
                          (Just g, Just (a, b)) -> Just $ g a b
                          _ ->
                            case (cast f, cast x :: Maybe a) of
                              (Just g, Just a) -> Just $ g a
                              _ -> Nothing

instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable h, Typeable i, Typeable j, Typeable k) => Curryable (a -> b -> c -> d -> e -> h -> i -> j -> k) where
  c f x =
    case (cast f, cast x :: Maybe (((((((a, b), c), d), e), h), i), j)) of
      (Just g, Just (((((((a, b), c), d), e), h), i), j)) -> Just $ g a b c d e h i j
      _ ->
        case (cast f, cast x :: Maybe ((((((a, b), c), d), e), h), i)) of
          (Just g, Just ((((((a, b), c), d), e), h), i)) -> Just $ g a b c d e h i
          _ ->
            case (cast f, cast x :: Maybe (((((a, b), c), d), e), h)) of
              (Just g, Just (((((a, b), c), d), e), h)) -> Just $ g a b c d e h
              _ ->
                case (cast f, cast x :: Maybe ((((a, b), c), d), e)) of
                  (Just g, Just ((((a, b), c), d), e)) -> Just $ g a b c d e
                  _ ->
                    case (cast f, cast x :: Maybe (((a, b), c), d)) of
                      (Just g, Just (((a, b), c), d)) -> Just $ g a b c d
                      _ ->
                        case (cast f, cast x :: Maybe ((a, b), c)) of
                          (Just g, Just ((a, b), c)) -> Just $ g a b c
                          _ ->
                            case (cast f, cast x :: Maybe (a, b)) of
                              (Just g, Just (a, b)) -> Just $ g a b
                              _ ->
                                case (cast f, cast x :: Maybe a) of
                                  (Just g, Just a) -> Just $ g a
                                  _ -> Nothing

instance {-# Overlaps #-} (Typeable a, Typeable b, Typeable c, Typeable d, Typeable e, Typeable h, Typeable i, Typeable j, Typeable k, Typeable l) => Curryable (a -> b -> c -> d -> e -> h -> i -> j -> k -> l) where
  c f x =
    case (cast f, cast x :: Maybe ((((((((a, b), c), d), e), h), i), j), k)) of
      (Just g, Just ((((((((a, b), c), d), e), h), i), j), k)) -> Just $ g a b c d e h i j k
      _ ->
        case (cast f, cast x :: Maybe (((((((a, b), c), d), e), h), i), j)) of
          (Just g, Just (((((((a, b), c), d), e), h), i), j)) -> Just $ g a b c d e h i j
          _ ->
            case (cast f, cast x :: Maybe ((((((a, b), c), d), e), h), i)) of
              (Just g, Just ((((((a, b), c), d), e), h), i)) -> Just $ g a b c d e h i
              _ ->
                case (cast f, cast x :: Maybe (((((a, b), c), d), e), h)) of
                  (Just g, Just (((((a, b), c), d), e), h)) -> Just $ g a b c d e h
                  _ ->
                    case (cast f, cast x :: Maybe ((((a, b), c), d), e)) of
                      (Just g, Just ((((a, b), c), d), e)) -> Just $ g a b c d e
                      _ ->
                        case (cast f, cast x :: Maybe (((a, b), c), d)) of
                          (Just g, Just (((a, b), c), d)) -> Just $ g a b c d
                          _ ->
                            case (cast f, cast x :: Maybe ((a, b), c)) of
                              (Just g, Just ((a, b), c)) -> Just $ g a b c
                              _ ->
                                case (cast f, cast x :: Maybe (a, b)) of
                                  (Just g, Just (a, b)) -> Just $ g a b
                                  _ ->
                                    case (cast f, cast x :: Maybe a) of
                                      (Just g, Just a) -> Just $ g a
                                      _ -> Nothing
