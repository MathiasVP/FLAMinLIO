{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module RPCExampleClient where

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
  asUser ("Mathias") $ do
    connect "127.0.0.1" "8000" "8001" $ \socket -> do
      withStrategy [bot] $ do
        clr <- getClearance
        toLabeled clr $ do
          rpc socket "create" (("Mathias" %) :: User) >>= \case
            Just (ack :: Response) -> liftIO $ print ack
            Nothing -> error "RPC failed!"

        
        toLabeled clr $ do
          rpc socket "open" (("Mathias" %) :: User) ("Savings" :: Account) >>= \case
            Just (ack :: Response) -> liftIO $ print ack
            Nothing -> error "RPC failed!"

        toLabeled "Mathias" $ do
          rpc socket "getBalance" (("Mathias" %) :: User) (("Savings" %) :: Account) >>= \case
            Just (bal :: Response) -> liftIO $ print bal
            Nothing -> error "RPC failed!"

        newScope $ do
          addDelegate ("Chloe" ←) ("Mathias" ←) bot
          addDelegate ("Chloe" →) ("Mathias" →) bot
          toLabeled clr $ do
            rpc socket "transfer" (("Mathias" %) :: User) ("Savings" :: Account)
                                  (("Chloe" %) :: User) ("Checking" :: Account)
                                  (50 :: Int) >>= \case
              Just (p :: Response) -> liftIO $ print p
              Nothing -> error "RPC failed!"
        
        toLabeled "Mathias" $ do
          rpc socket "getBalance" (("Mathias" %) :: User) ("Savings" :: Account) >>= \case
            Just (p :: Response) -> liftIO $ print p
            Nothing -> error "RPC failed!"

  liftIO getLine
  return ()

main :: IO ()
main = do
  h <- newMVar (H Set.empty)
  socks <- newMVar []
  evalStateT (runFLAM example h socks)
    (BoundedLabel { _cur = bot, _clearance = top }, noStrategy)
