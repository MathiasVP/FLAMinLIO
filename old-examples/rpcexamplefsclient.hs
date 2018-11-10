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
import FileSystem
import Data.Dynamic.Binary
import Data.Binary
import Data.String.Utils
import Control.Concurrent

asUser :: MonadFLAMIO m => String -> m () -> m ()
asUser u m = do
  label <- getLabel
  clr <- getClearance
  liftLIO $ modify $ _1 . clearance .~ (u %)
  _ <- m
  liftLIO $ modify $ _1 . clearance .~ (u %)
  liftLIO $ modify $ _1 . cur .~ label

example = do
  connect "127.0.0.1" "8000" "8001" $ \socket ->
    let handle = do
          liftIO $ putStrLn "Please type a command..."
          liftIO getLine >>= \case
            "up" -> do
              rpc socket "up" () >>= \case
                Just (r :: Bool) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            "down" -> do
              rpc socket "down" () >>= \case
                Just (r :: Bool) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            "left" -> do
              rpc socket "left" () >>= \case
                Just (r :: Bool) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            "right" -> do
              rpc socket "right" () >>= \case
                Just (r :: Bool) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            "ls" -> do
              rpc socket "ls" () >>= \case
                Just (r :: Maybe (File String)) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            "cat" -> do
              rpc socket "cat" () >>= \case
                Just (r :: Maybe String) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            't':'o':'u':'c':'h':name -> do
              p :: Principal <- read <$> liftIO getLine
              rpc socket "touch" p (lstrip name) >>= \case
                Just (r :: Bool) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            'm':'k':'d':'i':'r':name -> do
              p :: Principal <- read <$> liftIO getLine
              rpc socket "mkdir" p (lstrip name) >>= \case
                Just (r :: Bool) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            'w':'r':'i':'t':'e':' ':s -> do
              clr <- getClearance
              rpc socket "write" s >>= \case
                Just (r :: Bool) -> liftIO $ print r
                Nothing -> liftIO $ putStrLn "RPC failed!"
              handle
            'e':'x':'i':'t':[] -> return ()
            s -> do
              liftIO $ putStrLn $ "Command not understood: " ++ s
              handle
    in handle >> return ()
  
main :: IO ()
main = do
  h <- newMVar (H Set.empty)
  socks <- newMVar []
  evalStateT (runFLAM example h socks)
    (BoundedLabel { _cur = bot, _clearance = ("Mathias" %) }, noStrategy)
