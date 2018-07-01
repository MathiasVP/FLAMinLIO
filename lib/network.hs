{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE GADTs #-}
module Lib.Network where

import Lib.FLAM
import Lib.LIO
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Catch
import Control.Monad.Reader
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net
import Control.Lens.Tuple
import Control.Lens hiding ((:<))

class Serializable a where
  encode :: a -> B.ByteString
  decode :: B.ByteString -> Maybe a
  maxSize :: a -> Int

data LSocket a where
  LSocket :: Serializable a => (Net.Socket, Principal) -> LSocket a

data LSocketRPC where
  LSocketRPC :: (Net.Socket, Principal) -> LSocketRPC

type IP = String
type Name = String
type Port = String
type Host a = (IP, Port, a)

channelLabel :: LSocket a -> Principal
channelLabel (LSocket (_, s)) = s
  
serve :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocket a -> m r) -> m ()
serve (ip, port, name) f = do
  Net.listen (Net.Host ip) port (\(socket, addr) -> Net.accept socket (\(socket', _) -> f (LSocket (socket', (%) name))))
  return ()
  
connect :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocket a -> m r) -> m ()
connect (ip, port, name) f = do
  Net.connect ip port (\(socket, _) -> f (LSocket (socket, (%) name)))
  return ()

serveRPC :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocketRPC -> m r) -> m ()
serveRPC (ip, port, name) f = do
  Net.listen (Net.Host ip) port (\(socket, addr) -> Net.accept socket (\(socket', _) -> f (LSocketRPC (socket', (%) name))))
  return ()
  
connectRPC :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocketRPC -> m r) -> m ()
connectRPC (ip, port, name) f = do
  Net.connect ip port (\(socket, _) -> f (LSocketRPC (socket, (%) name)))
  return ()

instance MonadThrow m => MonadThrow (StepIndexT m) where
  throwM = StepIndexT . throwM
  
instance MonadCatch m => MonadCatch (StepIndexT m) where
  catch (StepIndexT m) f = StepIndexT $ catch m (unStepIndexT . f)
  
instance MonadMask m => MonadMask (StepIndexT m) where
  mask a = StepIndexT $ mask $ \u -> unStepIndexT (a $ q u)
    where q u (StepIndexT b) = StepIndexT (u b)

  uninterruptibleMask a = StepIndexT $ uninterruptibleMask $ \u -> unStepIndexT (a $ q u)
    where q u (StepIndexT b) = StepIndexT (u b)

  generalBracket acquire release use = StepIndexT $ generalBracket
    (unStepIndexT acquire)
    (\resource exitCase -> unStepIndexT (release resource exitCase))
    (\resource -> unStepIndexT (use resource))
  
instance MonadThrow FLAMIO where
  throwM = FLAMIO . throwM

instance MonadCatch FLAMIO where
  catch (FLAMIO m) f = FLAMIO $ catch m (unFLAMIO . f)

instance MonadMask FLAMIO where
  mask a = FLAMIO $ mask $ \u -> unFLAMIO (a $ q u)
    where q u (FLAMIO b) = FLAMIO (u b)

  uninterruptibleMask a = FLAMIO $ uninterruptibleMask $ \u -> unFLAMIO (a $ q u)
    where q u (FLAMIO b) = FLAMIO (u b)

  generalBracket acquire release use = FLAMIO $ generalBracket
    (unFLAMIO acquire)
    (\resource exitCase -> unFLAMIO (release resource exitCase))
    (\resource -> unFLAMIO (use resource))

{- Serialization instances for common types -}
instance Serializable Int where
  encode = BL.toStrict . Bin.encode
  decode x =
    case Bin.decodeOrFail (BL.fromStrict x) of
      Right (_, _, r) -> Just r
      _ -> Nothing
  maxSize _ = 8

instance Serializable Bool where
  encode = BL.toStrict . Bin.encode
  decode x = case Bin.decodeOrFail (BL.fromStrict x) of
      Right (_, _, r) -> Just r
      _ -> Nothing
  maxSize _ = 1

instance (Serializable a, Serializable b) => Serializable (a, b) where
  encode (a, b) = alen `B.append` a' `B.append` b'
    where a' = encode a
          b' = encode b
          alen = encode $ B.length a'

  decode bs =
    let (alen, rest) = B.splitAt (maxSize (undefined :: Int)) bs
    in case decode alen of
         Just (n :: Int) ->
           let (a, b) = B.splitAt n rest
           in case (decode a, decode b) of
                (Just a, Just b) -> Just (a, b)
                _ -> Nothing
         _ -> Nothing

  maxSize _ = maxSize (undefined :: Int) +
              maxSize (undefined :: a) +
              maxSize (undefined :: b)

instance (Serializable a, Serializable b, Serializable c) => Serializable (a, b, c) where
  encode (a, b, c) = alen `B.append` a' `B.append` encode (b, c)
    where a' = encode a
          alen = encode $ B.length a'
  decode bs =
    let (alen, rest) = B.splitAt (maxSize (undefined :: Int)) bs
    in case decode alen of
         Just (n :: Int) ->
           let (a, bc) = B.splitAt n rest
           in case (decode a, decode bc) of
                (Just a, Just (b, c)) -> Just (a, b, c)
                _ -> Nothing
         _ -> Nothing
          
  maxSize _ = maxSize (undefined :: Int) +
              maxSize (undefined :: a) +
              maxSize (undefined :: (b, c))

instance (Serializable a, Serializable b) => Serializable (Either a b) where
  encode (Left a) = B.cons 0 (encode a)
  encode (Right b) = B.cons 1 (encode b)

  decode bs =
    case B.uncons bs of
      Just (0, bs') -> Left <$> decode bs'
      Just (1, bs') -> Right <$> decode bs'
      _ -> Nothing

  maxSize _ = 1 + max (maxSize (undefined :: a)) (maxSize (undefined :: b))

instance Serializable String where
  encode = B8.pack
  decode = Just . B8.unpack
  maxSize _ = 1024

instance Serializable Principal where
  encode (:⊤) = B.singleton 0
  encode (:⊥) = B.singleton 1
  encode (Name s) = B.cons 2 (encode s)
  encode (p1 :/\ p2) = B.cons 3 (encode (p1, p2))
  encode (p1 :\/ p2) = B.cons 4 (encode (p1, p2))
  encode ((:→) p) = B.cons 5 (encode p)
  encode ((:←) p) = B.cons 6 (encode p)
  encode (p1 ::: p2) = B.cons 7 (encode (p1, p2))

  decode bs =
    case B.uncons bs of
      Just (0, _) -> Just (:⊤)
      Just (1, _) -> Just (:⊥)
      Just (2, bs') -> Name <$> decode bs'
      Just (3, bs') -> uncurry (:/\) <$> decode bs'
      Just (4, bs') -> uncurry (:\/) <$> decode bs'
      Just (5, bs') -> (:→) <$> decode bs'
      Just (6, bs') -> (:←) <$> decode bs'
      Just (7, bs') -> uncurry (:::) <$> decode bs'
      _ -> Nothing

  maxSize _ = 1024

instance Serializable () where
  encode () = B.empty
  decode = return $ Just ()
  maxSize _ = 0
  
instance Serializable a => Serializable (Labeled FLAM a) where
  encode (Labeled l a) = encode (l, a)
  decode bs = uncurry Labeled <$> decode bs
  maxSize _ = maxSize (undefined :: FLAM, undefined :: a)

instance MonadIO m => MonadIO (StepIndexT m) where
  liftIO = StepIndexT . liftIO

{- NOTE: This is a dangerous operation that should be put in a seperate (TCB) module! -}
instance MonadIO FLAMIO where
  liftIO = FLAMIO . liftIO
