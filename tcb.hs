{-# LANGUAGE StandaloneDeriving #-}
module TCB where

import LIO

deriving instance (Eq l, Eq a) => Eq (Labeled l a)
deriving instance (Ord l, Ord a) => Ord (Labeled l a)
deriving instance (Show l, Show a) => Show (Labeled l a)
