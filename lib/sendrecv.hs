{-# LANGUAGE DeriveGeneric #-}
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
import Control.Concurrent
import System.Random
import Control.Concurrent.Chan
import GHC.Generics
import Data.Typeable

data MsgType
  = RPCCall
  | RPCReturn
  | FwdQuery
  | FwdResponse
  | NewConn
  deriving (Generic)

instance Binary MsgType

send :: (MonadIO m, Binary a, Show a) => Chan BL.ByteString -> a -> MsgType -> m ()
send chan a typ =
  let d = encode a
  in liftIO $ writeChan chan (encode typ `BL.append`
                              encode (fromIntegral (BL.length d) :: Int) `BL.append` d)

recv :: forall m a . (Show a, MonadIO m, Binary a, Typeable a) => Chan BL.ByteString -> m (Maybe a)
recv chan = do
  bs <- liftIO $ readChan chan
  case decodeOrFail bs of
    Left (_, _, s) -> return Nothing
    Right (_, _, a) -> do
      return $ Just (a :: a)
