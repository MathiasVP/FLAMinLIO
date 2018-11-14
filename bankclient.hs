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
  liftLIO $ modify $ _1 . cur .~ ((⊥) →) ∧ (u ←)
  liftLIO $ modify $ _1 . clearance .~ (u →) ∧ ((⊥) ←)
  _ <- m
  liftLIO $ modify $ _1 . clearance .~ clr
  liftLIO $ modify $ _1 . cur .~ label

example :: FLAMIO ()
example = do
  asUser "Bob" $ do
    addDelegate "B" "Bob" ("Bob" ←)
  
  withStrategy [bot] $ do
    asUser "Alice" $ do
      connect "127.0.0.1" "8000" $ \socket -> do
        withStrategy [bot] $ do
          addDelegate "B" "Alice" ("Alice" ←)
          addDelegate ("Bob" →) ("Alice" →) ("Alice" ←)
        liftIO $ putStrLn "Logging in ..."
        rpc socket "login" "Alice" "password" >>= \case
          Just (tok :: Labeled Principal Principal) -> do
            liftIO $ putStrLn "Success!"
            withStrategy [bot] $ do
              liftIO $ putStrLn "Checking balance ..."
              rpc socket "balance" tok "Alice" >>= \case
                Just (Just n :: Maybe Int) -> do
                  liftIO $ putStrLn $ "Balance: " ++ show n
                  liftIO $ putStrLn "Transferring money"
                  rpc socket "transfer" tok "Alice" "Bob" (n `div` 2 :: Int) >>= \case
                    Just True -> liftIO $ putStrLn "Success!"
                    Nothing -> error "RPC error!"
                Just (Nothing :: Maybe Int) -> do
                  liftIO $ putStrLn $ "Error: Could not read balance!"
                Nothing -> error "RPC error!"
          Nothing -> error "RPC error!"
        
        liftIO getLine
        return ()

main :: IO ()
main = runFLAM "Alice" example
