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

getBalance :: User -> Account -> BankT FLAMIO Response
getBalance u a =
  Map.lookup u <$> get >>= \case
    Just lacc ->
      Map.lookup a <$> unlabel lacc >>= \case
        Just bal -> do
          liftIO $ putStrLn $ "Sending balance " ++ show bal
          return $ Balance bal
        Nothing -> do
          liftIO $ putStrLn $ "Sending NoSuchAccount"
          return $ NoSuchAccount
    Nothing -> do
      liftIO $ putStrLn $ "Sending NoSuchUser"
      return $ NoSuchUser

create :: User -> BankT FLAMIO Response
create u =
  Map.lookup u <$> get >>= \case
    Just _ -> do
      liftIO $ putStrLn $ "Sending UserAlreadyExists"
      return UserAlreadyExists
    Nothing -> do
      lacc <- label u Map.empty
      modify $ Map.insert u lacc
      liftIO $ putStrLn $ "Sending Ack"
      return Ack

open :: User -> Account -> BankT FLAMIO Response
open u a =
  Map.lookup u <$> get >>= \case
    Just lacc -> do
      acc <- unlabel lacc
      lacc' <- label u (Map.insert a 100 acc)
      modify $ Map.insert u lacc'
      liftIO $ putStrLn $ "Sending Ack"
      return Ack
    Nothing -> do
      liftIO $ putStrLn $ "Sending NoSuchUser"
      return NoSuchUser

transfer :: User -> Account -> User -> Account -> Int -> BankT FLAMIO Response
transfer uFrom aFrom uTo aTo n =
  Map.lookup uFrom <$> get >>= \case
    Just laccFrom -> do
      accFrom <- unlabel laccFrom
      case Map.lookup aFrom accFrom of
        Just balFrom
          | balFrom >= n -> do
              Map.lookup uTo <$> get >>= \case
                Just laccTo -> do
                  clr <- getClearance
                  toLabeled clr $ do
                    accTo <- unlabel laccTo
                    accTo' <- label uTo $ Map.update (Just . (+ n)) aTo accTo
                    modify $ Map.insert uTo accTo'
                  toLabeled clr $ do
                    accFrom' <- label uFrom $ Map.update (Just . (subtract n)) aFrom accFrom
                    modify $ Map.insert uFrom accFrom'
                  liftIO $ putStrLn $ "Sending Ack"
                  return Ack
                Nothing -> do
                  liftIO $ putStrLn $ "Sending NoSuchAccount"
                  return NoSuchAccount
          | otherwise -> do
              liftIO $ putStrLn $ "Sending NotSuccifientFunds"
              return NotSufficientFunds
        Nothing -> do
          liftIO $ putStrLn $ "Sending NoSuchAccount"
          return NoSuchAccount
    Nothing -> do
      liftIO $ putStrLn $ "Sending NoSuchUser"
      return NoSuchUser

example :: BankT FLAMIO ()
example = do
  create "Chloe"
  open "Chloe" "Checking"
  liftLIO $ modify $ _1 . cur .~ bot
  
  export "getBalance" (exportable2 getBalance)
  export "create" (exportable1 create)
  export "open" (exportable2 open)
  export "transfer" (exportable5 transfer)
  
  addDelegate ("Mathias" ←) ("Chloe" ←) "Mathias"

  serve ("127.0.0.1", "8000", (⊤), "8001") $ \socket -> do
    withStrategy ["Mathias"] $ do
      forever $ do
        recvRPC socket >>= \case
          Just (s, args) -> do
            lookupRPC s >>= \case
              Just g -> invoke g args >>= sendRPCResult socket
              Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic)
          Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic)

main :: IO ()
main =
  evalStateT (runFLAM $ evalStateT (runBankT example) Map.empty)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
