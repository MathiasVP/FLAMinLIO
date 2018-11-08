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

send :: (MonadIO m, Binary a) => Net.Socket -> a -> m ()
send socket a =
  let d = encode a
  in Net.sendLazy socket (BL.append (encode (fromIntegral (BL.length d) :: Int)) d)

recv :: forall m a . (MonadIO m, Binary a, Typeable a) => Net.Socket -> m (Maybe a)
recv socket = do
  Net.recv socket 8 >>= \case
    Just bs -> do
      case decodeOrFail (BL.fromStrict bs) of
        Left _ -> return Nothing
        Right (_, _, len :: Int) -> do
          Net.recv socket len >>= \case
            Just bs' -> do
              case decodeOrFail (BL.fromStrict bs') of
                          Left _ -> return Nothing
                          Right (_, _, ma) -> return $ Just ma
            Nothing -> return Nothing
    Nothing -> return Nothing
