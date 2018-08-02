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

asUser :: MonadFLAMIO m => String -> m () -> m ()
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
    forever $ do
      liftIO $ putStrLn "Please type a command..."
      liftIO getLine >>= \case
        "up" -> rpc socket "up" () >>= \case
                  Just (r :: Bool) -> liftIO $ print r
                  Nothing -> liftIO $ putStrLn "RPC failed!"
        "down" -> rpc socket "down" () >>= \case
                  Just (r :: Bool) -> liftIO $ print r
                  Nothing -> liftIO $ putStrLn "RPC failed!"
        "left" -> rpc socket "left" () >>= \case
                  Just (r :: Bool) -> liftIO $ print r
                  Nothing -> liftIO $ putStrLn "RPC failed!"
        "right" -> rpc socket "right" () >>= \case
                  Just (r :: Bool) -> liftIO $ print r
                  Nothing -> liftIO $ putStrLn "RPC failed!"
        "ls" -> rpc socket "ls" () >>= \case
                  Just (r :: Maybe (File String)) -> liftIO $ print r
                  Nothing -> liftIO $ putStrLn "RPC failed!"
        "cat" -> rpc socket "cat" () >>= \case
                  Just (r :: Maybe String) -> liftIO $ print r
                  Nothing -> liftIO $ putStrLn "RPC failed!"
        't':'o':'u':'c':'h':name -> do
          clr <- getClearance
          rpc socket "touch" clr (lstrip name) >>= \case
            Just (r :: Bool) -> liftIO $ print r
            Nothing -> liftIO $ putStrLn "RPC failed!"
        'm':'k':'d':'i':'r':name -> do
          clr <- getClearance
          rpc socket "mkdir" clr (lstrip name) >>= \case
            Just (r :: Bool) -> liftIO $ print r
            Nothing -> liftIO $ putStrLn "RPC failed!"
        'w':'r':'i':'t':'e':' ':s -> do
          clr <- getClearance
          rpc socket "write" s >>= \case
            Just (r :: Bool) -> liftIO $ print r
            Nothing -> liftIO $ putStrLn "RPC failed!"
            
    liftIO getLine
    return ()
  
main :: IO ()
main =
  evalStateT (runFLAM example)
    (BoundedLabel { _cur = bot, _clearance = ("Mathias" %) }, H Set.empty, noStrategy)
