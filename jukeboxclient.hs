{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module JukeBoxClient where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Lens
import JukeBox
import Data.Dynamic.Binary
import Data.Binary
import Control.Concurrent.MVar

asUser :: ToLabel a Principal => MonadFLAMIO m => a -> m () -> m ()
asUser u m = do
  label <- getLabel
  clr <- getClearance
  liftLIO $ modify $ _1 . clearance .~ (u →) ∧ ((⊥) ←)
  _ <- m
  liftLIO $ modify $ _1 . clearance .~ clr
  liftLIO $ modify $ _1 . cur .~ label

example :: FLAMIO ()
example = do
  lbl <- getLabel
  withStrategy [lbl] $ do
    asUser "M" $ do
      addDelegate ("J" ←) ("M" ←) lbl
      addDelegate ("J" →) ("M" →) lbl
      song <- label ("M" →) "Taylor Swift - Shake it Off"
      liftIO getLine
      connect "127.0.0.1" "8000" $ \socket -> do
        rpc socket "vote" song >>= \case
          Just (b :: Bool) -> liftIO $ putStrLn "Voted for song"
          Nothing -> liftIO $ putStrLn "RPC error!"

      liftIO getLine
      return ()

main :: IO ()
main = runFLAM "M" example
