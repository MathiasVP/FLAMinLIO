{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Lib.TCB where

import Lib.LIO
import Control.Monad.IO.Class

deriving instance (Eq l, Eq a) => Eq (Labeled l a)
deriving instance (Ord l, Ord a) => Ord (Labeled l a)
deriving instance (Show l, Show a) => Show (Labeled l a)

instance Label s l => MonadIO (LIO s l) where
  liftIO = LIO . liftIO
