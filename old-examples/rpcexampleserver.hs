{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module RPCExampleServer where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Map as Map
import Control.Lens
import Bank
import Data.Typeable
import Data.Dynamic.Binary
import Control.Concurrent

getBalance :: User -> Account -> BankT FLAMIO Response
getBalance u a = do
  mvar <- get
  Map.lookup u <$> liftIO (readMVar mvar) >>= \case
    Just lacc ->
      Map.lookup a <$> unlabel lacc >>= \case
        Just bal -> return $ Balance bal
        Nothing -> return $ NoSuchAccount
    Nothing -> return $ NoSuchUser

create :: User -> BankT FLAMIO Response
create u = do
  mvar <- get
  bankdata <- liftIO $ takeMVar mvar
  case Map.lookup u bankdata of
    Just _ -> do
      liftIO $ putMVar mvar bankdata
      return UserAlreadyExists
    Nothing -> do
      lacc <- label u Map.empty
      liftIO $ putMVar mvar $ Map.insert u lacc bankdata
      return Ack

open :: User -> Account -> BankT FLAMIO Response
open u a = do
  mvar <- get
  bankdata <- liftIO $ takeMVar mvar
  case Map.lookup u bankdata of
    Just lacc -> do
      acc <- unlabel lacc
      case Map.lookup a acc of
        Just _ -> do
          liftIO $ putMVar mvar bankdata
          return AccountAlreadyExists
        Nothing -> do
          lacc' <- label u (Map.insert a 100 acc)
          liftIO $ putMVar mvar $ Map.insert u lacc' bankdata
          return Ack
    Nothing -> do
      liftIO $ putMVar mvar bankdata
      return NoSuchUser

transfer :: User -> Account -> User -> Account -> Int -> BankT FLAMIO Response
transfer uFrom aFrom uTo aTo n = do
  mvar <- get
  bankdata <- liftIO $ takeMVar mvar
  case Map.lookup uFrom bankdata of
    Just laccFrom -> do
      accFrom <- unlabel laccFrom
      case Map.lookup aFrom accFrom of
        Just balFrom
          | balFrom >= n -> do
              case Map.lookup uTo bankdata of
                Just laccTo -> do
                  clr <- getClearance
                  toLabeled clr $ do
                    accTo <- unlabel laccTo
                    accTo' <- label uTo $ Map.update (Just . (+ n)) aTo accTo
                    liftIO $ putMVar mvar $ Map.insert uTo accTo' bankdata
                  toLabeled clr $ do
                    bankdata <- liftIO $ takeMVar mvar
                    accFrom' <- label uFrom $ Map.update (Just . (subtract n)) aFrom accFrom
                    liftIO $ putMVar mvar $ Map.insert uFrom accFrom' bankdata
                  return Ack
                Nothing -> return NoSuchAccount
          | otherwise -> return NotSufficientFunds
        Nothing -> return NoSuchAccount
    Nothing -> return NoSuchUser

repeatUntilM :: Monad m => m Bool -> m ()
repeatUntilM m =
  m >>= \case
    True -> repeatUntilM m
    False -> return ()

example :: BankT FLAMIO ()
example = do
  toLabeled top $ do
    create ("Chloe" %)
    open ("Chloe" %) "Checking"
  toLabeled top $ do
    withStrategy [bot] $ do
      addDelegate ("Mathias" ←) ("Chloe" ←) bot
      addDelegate ("Mathias" →) ("Chloe" →) bot
  
  export "getBalance" (exportable2 getBalance)
  export "create" (exportable1 create)
  export "open" (exportable2 open)
  export "transfer" (exportable5 transfer)

  forever $ do
    serve "127.0.0.1" "8000" "8001" $ \socket -> do
      toLabeled top $ do
        repeatUntilM $ do
          withStrategy [bot] $ do
            recvRPC socket >>= \case
              Just (Just (s, args)) -> do
                x <- get
                y <- liftIO $ readMVar x
                liftIO $ print y
                lookupRPC s >>= \case
                  Just g -> invoke g args >>= sendRPCResult socket >> return True
                  Nothing -> sendRPCResult socket Nothing >> return True
              Just Nothing -> return False
              Nothing -> sendRPCResult socket Nothing >> return True
  return ()
  
main :: IO ()
main = do
  bankdata <- newMVar Map.empty
  runFLAM (evalStateT (runBankT example) bankdata)
