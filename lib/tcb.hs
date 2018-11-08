{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
module Lib.TCB where

import Lib.LIO
import Control.Monad.IO.Class

deriving instance (Eq l, Eq a) => Eq (Labeled l a)
deriving instance (Ord l, Ord a) => Ord (Labeled l a)
deriving instance (Show l, Show a) => Show (Labeled l a)

instance Label l => MonadIO (LIO l) where
  liftIO = LIO . liftIO
