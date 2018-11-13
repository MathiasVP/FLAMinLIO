{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module Government where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Lens
import Data.Dynamic.Binary
import Data.Binary

asUser :: ToLabel a Principal => MonadFLAMIO m => a -> m () -> m ()
asUser u m = do
  label <- getLabel
  clr <- getClearance
  liftLIO $ modify $ _1 . cur .~ ((⊥) →) ∧ (u ←)
  liftLIO $ modify $ _1 . clearance .~ (u →) ∧ ((⊥) ←)
  _ <- m
  liftLIO $ modify $ _1 . clearance .~ clr
  liftLIO $ modify $ _1 . cur .~ label

example :: FLAMIO ()
example = do
  asUser "CIA" $ do
    addDelegate ("CIA" .: "B") "CIA" "CIA"
    addDelegate ("CIA" .: "A") "CIA" "CIA"

  asUser ("CIA" .: "A") $ do
    withStrategy ["CIA"] $ do
      x <- ("CIA" .: "B") ≽ "CIA"
      liftIO $ print x
  

main :: IO ()
main = runFLAM "CIA" example
