{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import System.IO
import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.SendRecv
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
                liftIO $ putStrLn $ "Sending balance " ++ show bal
                send socket clr (Right $ Balance bal)
              Nothing -> do
                liftIO $ putStrLn $ "Sending NoSuchAccount"
                send socket clr (Right NoSuchAccount)
          Nothing -> do
            liftIO $ putStrLn $ "Sending NoSuchUser"
            send socket clr (Right NoSuchUser)
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
                        liftIO $ putStrLn $ "Sending Ack"
                        send socket clr (Right Ack)
                      Nothing -> do
                        liftIO $ putStrLn $ "Sending NoSuchAccount"
                        send socket clr (Right NoSuchAccount)
                | otherwise -> do
                    liftIO $ putStrLn $ "Sending NotSuccifientFunds"
                    send socket clr (Right NotSufficientFunds)
              Nothing -> do
                liftIO $ putStrLn $ "Sending NoSuchAccount"
                send socket clr (Right NoSuchAccount)
          Nothing -> do
            liftIO $ putStrLn $ "Sending NoSuchUser"
            send socket clr (Right NoSuchUser)
        inSession socket
      Left (Create u) -> do
        Map.lookup u <$> get >>= \case
          Just _ -> do
            liftIO $ putStrLn $ "Sending UserAlreadyExists"
            send socket clr (Right UserAlreadyExists)
          Nothing -> do
            lacc <- label u Map.empty
            modify $ Map.insert u lacc
            liftIO $ putStrLn $ "Sending Ack"
            send socket clr (Right Ack)
        inSession socket
      Left (OpenAccount u a) -> do
        Map.lookup u <$> get >>= \case
          Just lacc -> do
            acc <- unlabel lacc
            lacc' <- label u (Map.insert a 0 acc)
            modify $ Map.insert u lacc'
            liftIO $ putStrLn $ "Sending Ack"
            send socket clr (Right Ack)
          Nothing -> do
            liftIO $ putStrLn $ "Sending NoSuchUser"
            send socket clr (Right NoSuchUser)
        inSession socket
      Left (CloseAccount u a) -> do
        Map.lookup u <$> get >>= \case
          Just lacc -> do
            acc <- unlabel lacc
            case Map.lookup a acc of
              Just 0 -> do
                lacc' <- label clr (Map.delete a acc)
                modify $ Map.update (const $ Just lacc') u
                liftIO $ putStrLn $ "Sending Ack"
                send socket clr (Right Ack)
              Nothing -> do
                liftIO $ putStrLn $ "Sending NonEmptyAccount"
                send socket clr (Right NonEmptyAccount)
          Nothing -> do
            liftIO $ putStrLn $ "Sending NoSuchUser"
            send socket clr (Right NoSuchUser)
        inSession socket
      Left (StartSession _) -> do
        liftIO $ putStrLn $ "Sending ProtocolError"
        send socket clr (Right ProtocolError)
        inSession socket
      Left EndSession -> do
        liftIO $ putStrLn $ "Sending Ack"
        send socket clr (Right Ack)
        return ()
      Right _ -> do
        liftIO $ putStrLn $ "Sending ProtocolError"
        send socket clr (Right ProtocolError)
        inSession socket
    _ -> return ()

await :: LSocket (Either Request Response) -> BankT FLAMIO ()
await socket = do
  recv socket >>= \case
    Just lab -> do
      newScope $ do
         unlabel lab >>= \case
          Left (StartSession u) -> do
            lbl <- getLabel
            clr <- getClearance
            send socket u (Right Ack)
            liftLIO $ modify $ _1 . clearance .~ (u %)
            inSession socket
            liftLIO $ modify $ _1 . cur .~ lbl
            liftLIO $ modify $ _1 . clearance .~ clr
    Nothing -> await socket

report :: String -> BankT FLAMIO ()
report s = liftIO $ putStrLn s

example :: BankT FLAMIO ()
example = do
  liftIO $ hSetBuffering stdout NoBuffering
  withStrategy [bot] $ do
    report "1"
    addDelegate ("BankClient" ←) ("BankServer" ←) bot
    report "1"
    serve ("127.0.0.1", "8000", ("BankClient" →) /\ ((⊥) ←)) $ \socket -> do
      recvDelegate socket >>= \case
        True -> do
          report "2"
          sendDelegate socket ("BankClient" →) ("BankServer" →) bot
          report "2"
          -- Now: BankClient ⊑ BankServer @ bot
          recv socket >>= \case
            Just lab -> do
              report "3"
              unlabel lab >>= \case
                Left (StartSession u) -> do
                  report "3"
                  report "4"
                  --addDelegate (u ←) ("BankServer" ←) "BankClient"
                  report "4"
                  report "5"
                  recvDelegate socket >>= \case
                    True -> do
                      report "5"
                      report "6"
                      withStrategy [("BankClient" %) :: Principal] $ do
                        -- Now: u ⊑ BankServer @ BankClient
                        report "7"
                        newScope $ do
                          addDelegate (u ←) ("BankServer" ←) "BankClient"
                          sendDelegate socket (u →) ("BankServer" →) "BankClient"
                        report "7"
                        report "8"
                        sendDelegate socket ("BankClient" ←) ("BankServer" ←) "BankClient"
                        recvDelegate socket >>= \case
                          True -> do
                            report "8"
                            report "9"
                            withStrategy [u] $ do
                              addDelegate (u →) ("BankClient" →) ("BankClient" ⊔ u :: Principal)
                              report "9"
                              report "10"
                              addDelegate ("BankClient" ←) (u ←) ("BankClient" ⊔ u :: Principal)
                              report "10"
                              -- Now: BankClient ⊑ u @ BankClient ⊔ u (So BankClient ⊑ u @ u)
                              report "11"
                              addDelegate ("BankClient" →) (u →) u
                              send socket u (Right Ack)
                              report "11"
                              lbl <- getLabel
                              clr <- getClearance
                              liftLIO $ modify $ _1 . clearance .~ (u %)
                              inSession socket
                              liftLIO $ modify $ _1 . cur .~ lbl
                              liftLIO $ modify $ _1 . clearance .~ clr
                          False -> error "Error receiving delegation!"
                          
                    False -> error "Could not receive delegation!"
            Nothing -> error "Error recv'ing!"
          
        False -> error "Could not receive delegation!"
      await socket
  return ()

main :: IO ()
main =
  evalStateT (unLIO (runFLAM (execBankT example Map.empty)))
  (BoundedLabel { _cur = bot, _clearance = ("BankServer" %) }, H Set.empty, noStrategy) >>= print
