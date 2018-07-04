{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lib.Serializable where

import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Data.Binary as Bin
import qualified Data.List as List
import Data.Typeable

class Serializable a where
  encode :: a -> B.ByteString
  decode' :: B.ByteString -> Maybe (a, B.ByteString)
  decode :: B.ByteString -> Maybe a
  decode bs =
    case decode' bs of
      Just (a, bs) | bs == B.empty -> Just a
      _ -> Nothing
  maxSize :: a -> Int

data SerializableExt = forall t . (Serializable t, Typeable t, Show t) => SerializableExt t

instance Show SerializableExt where
  show (SerializableExt x) = "SerializableExt (" ++ show x ++ ")"

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
