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
  liftLIO $ modify $ _1 . cur .~ ((⊥) →) ∧ (u ←)
  liftLIO $ modify $ _1 . clearance .~ (u →) ∧ ((⊥) ←)
  _ <- m
  liftLIO $ modify $ _1 . clearance .~ clr
  liftLIO $ modify $ _1 . cur .~ label

example :: FLAMIO ()
example = do
  asUser "M" $ do
    lbl <- getLabel
    withStrategy [lbl] $ do
      addDelegate ("J" →) ("M" →) lbl
      song <- label "M" "Taylor Swift - Shake it Off"
      connect "127.0.0.1" "8000" $ \socket -> do
        rpc socket "vote" song >>= \case
          Just (b :: Bool) -> liftIO $ putStrLn "Voted for song"
          Nothing -> liftIO $ putStrLn "RPC error!"

  asUser "I" $ do
    lbl <- getLabel
    withStrategy [lbl] $ do
      addDelegate ("J" →) ("I" →) lbl
      song <- label "I" "Taylor Swift - Shake it Off"
      connect "127.0.0.1" "8000" $ \socket -> do
        rpc socket "vote" song >>= \case
          Just (b :: Bool) -> liftIO $ putStrLn "Voted for song"
          Nothing -> liftIO $ putStrLn "RPC error!"

  asUser "F" $ do
    lbl <- getLabel
    withStrategy [lbl] $ do
      addDelegate ("J" →) ("F" →) lbl
      song <- label "F" "Linkin Park - In the End"
      connect "127.0.0.1" "8000" $ \socket -> do
        rpc socket "vote" song >>= \case
          Just (b :: Bool) -> liftIO $ putStrLn "Voted for song"
          Nothing -> liftIO $ putStrLn "RPC error!"

  asUser "M" $ do
    lbl <- getLabel
    withStrategy [lbl] $ do
      connect "127.0.0.1" "8000" $ \socket -> do
        rpc socket "play" (0 :: Int) >>= \case
          Just (s :: String) -> liftIO $ putStrLn $ "Playing song: " ++ show s
          Nothing -> liftIO $ putStrLn "RPC error!"

main :: IO ()
main = runFLAM "M" example
