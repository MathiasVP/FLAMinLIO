{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module BankServer where

import Lib.FLAM
import Lib.LIO
import qualified Data.Set as Set
import qualified Data.Map as Map
import Bank
import Control.Monad.State
import Control.Lens
import Control.Lens.Traversal

inSession :: LSocket (Either Request Response) -> BankT FLAMIO ()
inSession socket = do
  clr <- getClearance
  recv socket >>= \case
    Just lab -> unlabel lab >>= \case
      Left (GetBalance u a) -> do
        Map.lookup u <$> get >>= \case
          Just lacc ->
            Map.lookup a <$> unlabel lacc >>= \case
              Just bal -> do
                send socket clr (Right $ Balance bal)
              Nothing -> send socket clr (Right NoSuchAccount)
          Nothing -> send socket clr (Right NoSuchUser)
        inSession socket
      Left (Transfer n (uFrom, aFrom) (uTo, aTo)) -> do
        Map.lookup uFrom <$> get >>= \case
          Just laccFrom -> do
            accFrom <- unlabel laccFrom
            case Map.lookup aFrom accFrom of
              Just balFrom
                | balFrom >= n -> do
                    Map.lookup uTo <$> get >>= \case
                      Just laccTo -> do
                        accTo <- unlabel laccTo
                        accTo' <- label uTo $ Map.update (Just . (+ n)) aTo accTo
                        modify $ Map.insert uTo accTo'
                        accFrom' <- label uFrom $ Map.update (Just . (subtract n)) aFrom accFrom
                        modify $ Map.insert uFrom accFrom'
                        send socket clr (Right Ack)
                      Nothing -> send socket clr (Right NoSuchAccount)
                | otherwise -> send socket clr (Right NotSufficientFunds)
              Nothing -> send socket clr (Right NoSuchAccount)
          Nothing -> send socket clr (Right NoSuchUser)
        inSession socket
      Left (OpenAccount u a) -> do
        Map.lookup u <$> get >>= \case
          Just lacc -> do
            acc <- unlabel lacc
            lacc' <- label u (Map.insert a 0 acc)
            modify $ Map.insert u lacc'
          Nothing -> send socket clr (Right NoSuchUser)
        inSession socket
      Left (CloseAccount u a) -> do
        Map.lookup u <$> get >>= \case
          Just lacc -> do
            acc <- unlabel lacc
            case Map.lookup a acc of
              Just 0 -> do
                lacc' <- label clr (Map.delete a acc)
                modify $ Map.update (const $ Just lacc') u
              Nothing -> send socket clr (Right NonEmptyAccount)
          Nothing -> send socket clr (Right NoSuchUser)
        inSession socket
      Left (StartSession _) -> do
        send socket clr (Right ProtocolError)
        inSession socket
      Left EndSession -> do
        send socket clr (Right Ack)
        return ()
      Right _ -> do
        send socket clr (Right ProtocolError)
        inSession socket
    _ -> return ()

await :: LSocket (Either Request Response) -> BankT FLAMIO ()
await socket = do
  recv socket >>= \case
    Just lab -> unlabel lab >>= \case
      Left (StartSession u) -> do
        lbl <- getLabel
        clr <- getClearance
        send socket u (Right Ack)
        liftLIO $ modify $ _1 . clearance .~ (u %)
        inSession socket
        liftLIO $ modify $ _1 . cur .~ lbl
        liftLIO $ modify $ _1 . clearance .~ clr
    _ -> await socket
  
    
example :: BankT FLAMIO ()
example = do
  addDelegate (("Client" →), ("Server" →)) bot
  addDelegate (("Server" ←), ("Client" ←)) bot
  withStrategy (Strategy [bot]) $ do
    serve ("127.0.0.1", "8000", "BankClient") await
  return ()

runExample :: IO ()
runExample =
  evalStateT (unLIO (runFLAM (execBankT example Map.empty)))
  (BoundedLabel { _cur = bot, _clearance = ("BankServer" %) }, H Set.empty, noStrategy) >>= print
