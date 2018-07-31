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
import Control.Lens
import Bank
import Data.Dynamic.Binary
import Data.Binary

asUser :: MonadFLAMIO m => User -> m () -> m ()
asUser u m = do
  label <- getLabel
  clr <- getClearance
  liftLIO $ modify $ _1 . clearance .~ (u %)
  _ <- m
  liftLIO $ modify $ _1 . clearance .~ (u %)
  liftLIO $ modify $ _1 . cur .~ label

example :: FLAMIO ()
example = do
  connect ("127.0.0.1", "8000", (⊤), "8001") $ \socket -> do
    asUser "Mathias" $ do
      rpc socket "create" ("Mathias" :: User) >>= \case
        Just (ack :: Response) -> liftIO $ print ack
        Nothing -> error "RPC failed!"

      rpc socket "open" ("Mathias" :: User) ("Savings" :: Account) >>= \case
        Just (ack :: Response) -> liftIO $ print ack
        Nothing -> error "RPC failed!"
        
      rpc socket "getBalance" ("Mathias" :: User) ("Savings" :: Account) >>= \case
        Just (bal :: Response) -> liftIO $ print bal
        Nothing -> error "RPC failed!"

      newScope $ do
        withStrategy ["Mathias"] $ do
          addDelegate ("Chloe" ←) ("Mathias" ←) "Mathias"
          addDelegate ("Chloe" →) ("Mathias" →) "Mathias"

          rpc socket "transfer" ("Mathias" :: User) ("Savings" :: Account)
                                ("Chloe" :: User) ("Checking" :: Account)
                                (50 :: Int) >>= \case
            Just (p :: Response) -> liftIO $ print p
            Nothing -> error "RPC failed!"

      rpc socket "getBalance" ("Mathias" :: User) ("Savings" :: Account) >>= \case
        Just (p :: Response) -> liftIO $ print p
        Nothing -> error "RPC failed!"

      liftIO getLine
      return ()

  liftIO getLine
  return ()
  connect ("127.0.0.1", "8000", (⊤), "8001") $ \socket -> do
    asUser "Chloe" $ do
      rpc socket "getBalance" ("Chloe" :: User) ("Checking" :: Account) >>= \case
        Just (bal :: Response) -> liftIO $ print bal
        Nothing -> error "RPC failed!"
      liftIO getLine
      return ()

main :: IO ()
main =
  evalStateT (runFLAM example)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
