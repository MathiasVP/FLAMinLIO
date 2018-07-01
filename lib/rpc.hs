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
import Lib.Network
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Catch
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net
import Control.Lens.Tuple
import Control.Lens hiding ((:<))

class RPCType a where
  rpc' :: Serializable b => LSocketRPC -> String -> b -> a

instance (Serializable a, RPCType r) => RPCType (a -> r) where
  rpc' socket f arg1 = \arg2 -> rpc' socket f (arg1, arg2)

instance Serializable a => RPCType (IO (Maybe a)) where
  rpc' (LSocketRPC (s, name)) f args = do
    Net.send s (encode (f, args))
    Net.recv s (maxSize (undefined :: a)) >>= \case
      Just bs -> return $ decode bs
      Nothing -> return Nothing
