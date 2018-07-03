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
import qualified Data.List as List
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
import Data.Tuple.Only
import Control.Lens hiding ((:<))
import Data.Typeable

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
  Net.listen (Net.Host ip) port (\(socket, addr) ->
    Net.accept socket (\(socket', _) ->
      let lsocket = LSocketRPC (socket', (%) name)
      in putSocketRPC lsocket >> f lsocket >> removeSocketRPC lsocket))
  return ()
  
connectRPC :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocketRPC -> m r) -> m ()
connectRPC (ip, port, name) f = do
  Net.connect ip port (\(socket, _) ->
    let lsocket = LSocketRPC (socket, (%) name)
    in putSocketRPC lsocket >> f lsocket >> removeSocketRPC lsocket)
  return ()

instance MonadThrow m => MonadThrow (AssumptionsT m) where
  throwM = AssumptionsT . throwM
  
instance MonadCatch m => MonadCatch (AssumptionsT m) where
  catch (AssumptionsT m) f = AssumptionsT $ catch m (unAssumptionsT . f)
  
instance MonadMask m => MonadMask (AssumptionsT m) where
  mask a = AssumptionsT $ mask $ \u -> unAssumptionsT (a $ q u)
    where q u (AssumptionsT b) = AssumptionsT (u b)

  uninterruptibleMask a = AssumptionsT $ uninterruptibleMask $ \u -> unAssumptionsT (a $ q u)
    where q u (AssumptionsT b) = AssumptionsT (u b)

  generalBracket acquire release use = AssumptionsT $ generalBracket
    (unAssumptionsT acquire)
    (\resource exitCase -> unAssumptionsT (release resource exitCase))
    (\resource -> unAssumptionsT (use resource))
  
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
  decode' bs =
    case Bin.decodeOrFail (BL.fromStrict bs) of
      Right (bs', _, r) -> Just (r, BL.toStrict bs')
      _ -> Nothing
  maxSize _ = 8

instance Serializable Bool where
  encode = BL.toStrict . Bin.encode
  decode' bs = case Bin.decodeOrFail (BL.fromStrict bs) of
      Right (bs', _, r) -> Just (r, BL.toStrict bs')
      _ -> Nothing
  maxSize _ = 1

instance Serializable Char where
  encode = BL.toStrict . Bin.encode
  decode' bs = case Bin.decodeOrFail (BL.fromStrict bs) of
      Right (bs', _, r) -> Just (r, BL.toStrict bs')
      _ -> Nothing
  maxSize _ = 4

instance (Serializable a, Serializable b) => Serializable (a, b) where
  encode (a, b) = alen `B.append` a' `B.append` b'
    where a' = encode a
          b' = encode b
          alen = encode $ B.length a'

  decode' bs =
    let (alen, rest) = B.splitAt (maxSize (undefined :: Int)) bs
    in case decode alen of
         Just (n :: Int) ->
           let (a, b) = B.splitAt n rest
           in case (decode a, decode' b) of
                (Just a, Just (b, bs')) -> Just ((a, b), bs')
                _ -> Nothing
         _ -> Nothing

  maxSize _ = maxSize (undefined :: Int) +
              maxSize (undefined :: a) +
              maxSize (undefined :: b)

instance (Serializable a, Serializable b, Serializable c) => Serializable (a, b, c) where
  encode (a, b, c) = alen `B.append` a' `B.append` encode (b, c)
    where a' = encode a
          alen = encode $ B.length a'
  decode' bs =
    let (alen, rest) = B.splitAt (maxSize (undefined :: Int)) bs
    in case decode alen of
         Just (n :: Int) ->
           let (a, bc) = B.splitAt n rest
           in case (decode a, decode' bc) of
                (Just a, Just ((b, c), bs')) -> Just ((a, b, c), bs')
                _ -> Nothing
         _ -> Nothing
          
  maxSize _ = maxSize (undefined :: Int) +
              maxSize (undefined :: a) +
              maxSize (undefined :: (b, c))

(</>) :: Functor f => (a -> b) -> f (a, c) -> f (b, c)
f </> p = fmap (\(a, c) -> (f a, c)) p

instance Serializable a => Serializable (Only a) where
  encode (Only a) = encode a
  decode' bs = Only </> decode' bs

  maxSize _ = maxSize (undefined :: a)

instance (Serializable a, Serializable b) => Serializable (Either a b) where
  encode (Left a) = B.cons 0 (encode a)
  encode (Right b) = B.cons 1 (encode b)

  decode' bs =
    case B.uncons bs of
      Just (0, bs') -> do
        Left </> decode' bs'
      Just (1, bs') -> do
        Right </> decode' bs'
      _ -> Nothing

  maxSize _ = 1 + max (maxSize (undefined :: a)) (maxSize (undefined :: b))

instance Serializable Principal where
  encode (:⊤) = B.singleton 0
  encode (:⊥) = B.singleton 1
  encode (Name s) = B.cons 2 (encode s)
  encode (p1 :/\ p2) = B.cons 3 (encode (p1, p2))
  encode (p1 :\/ p2) = B.cons 4 (encode (p1, p2))
  encode ((:→) p) = B.cons 5 (encode p)
  encode ((:←) p) = B.cons 6 (encode p)
  encode (p1 ::: p2) = B.cons 7 (encode (p1, p2))

  decode' bs =
    case B.uncons bs of
      Just (0, bs') -> Just ((:⊤), bs')
      Just (1, bs') -> Just ((:⊥), bs')
      Just (2, bs') -> Name </> decode' bs'
      Just (3, bs') -> uncurry (:/\) </> decode' bs'
      Just (4, bs') -> uncurry (:\/) </> decode' bs'
      Just (5, bs') -> (:→) </> decode' bs'
      Just (6, bs') -> (:←) </> decode' bs'
      Just (7, bs') -> uncurry (:::) </> decode' bs'
      _ -> Nothing

  maxSize _ = 1024

instance Serializable () where
  encode () = B.empty
  decode' bs' = Just ((), bs')
  maxSize _ = 0

instance Serializable a => Serializable [a] where
  encode xs = encode n `B.append` foldMap encode xs
    where n = List.length xs
  decode' bs =
    let (nenc, rest) = B.splitAt (maxSize (undefined :: Int)) bs
        work :: Int -> B.ByteString -> Maybe ([a], B.ByteString)
        work 0 bs = pure </> decode' bs
        work k bs = decode' bs >>= \(a, bs') -> ((:) a) </> work (k - 1) bs'
    in do
      n <- decode nenc :: Maybe Int
      work (n - 1) rest
  maxSize _ = 1024

instance Serializable a => Serializable (Maybe a) where
  encode Nothing = B.singleton 0
  encode (Just a) = B.cons 1 (encode a)

  decode' bs =
    case B.uncons bs of
      Just (0, bs') -> Just (Nothing, bs')
      Just (1, bs') -> Just </> decode' bs'

  maxSize _ = 1 + maxSize (undefined :: a)

instance Serializable a => Serializable (Labeled FLAM a) where
  encode (Labeled l a) = encode (l, a)
  decode' bs = uncurry Labeled </> decode' bs
  maxSize _ = maxSize (undefined :: FLAM, undefined :: a)  

instance MonadIO m => MonadIO (AssumptionsT m) where
  liftIO = AssumptionsT . liftIO

{- NOTE: This is a dangerous operation that should be put in a seperate (TCB) module! -}
instance MonadIO FLAMIO where
  liftIO = FLAMIO . liftIO
