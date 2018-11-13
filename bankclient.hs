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
import Bank
import Data.Dynamic.Binary
import Data.Binary

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
  asUser "Bob" $ do
    withStrategy [bot] $ do
      addDelegate ("B" →) ("Bob" →) bot

  withStrategy [bot] $ do
    asUser "Alice" $ do
      connect "127.0.0.1" "8000" $ \socket -> do
        withStrategy [bot] $ do
          addDelegate ("B" →) ("Alice" →) bot

          addDelegate ("Bob" →) ("Alice" →) bot
        rpc socket "login" "Alice" "password" >>= \case
          Just (tok :: Labeled Principal Principal) -> do
            withStrategy [bot] $ do
              rpc socket "balance" tok "Alice" >>= \case
                Just (n :: Maybe Int) -> do
                  rpc socket "transfer" tok "Alice" "Bob" (25 :: Int) >>= \case
                    Just (b :: Bool) -> liftIO $ print b
                    Nothing -> error "RPC error!"
                Nothing -> error "RPC error!"
          Nothing -> error "RPC error!"
        
        liftIO getLine
        return ()

main :: IO ()
main = runFLAM "Alice" example
