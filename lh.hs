module LH where

import LIO

data LH = L | H
  deriving Show

instance Label LH where
  L ⊑ L = True
  L ⊑ H = True
  H ⊑ H = True
  _ ⊑ _ = False

  L ⊔ L = L
  _ ⊔ _ = H

  H ⊓ H = H
  _ ⊓ _ = L
