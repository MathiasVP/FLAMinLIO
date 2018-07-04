{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import System.IO
import Lib.FLAM
import Lib.LIO
import qualified Data.Set as Set
import qualified Data.Map as Map
import Bank
import Control.Monad.State
import Control.Lens
import Control.Lens.Traversal
import Data.Char

inSession :: LSocket (Either Request Response) -> BankT FLAMIO ()
inSession socket = do
  clr <- getClearance
  liftIO $ putStr $ unlines ["Choose option:",
                             "  Balance",
                             "  Transfer",
                             "  Create",
                             "  Open",
                             "  Close",
                             "  Exit"]
  liftIO getLine >>= \case
    "Balance" -> do
      liftIO $ putStr "User: "
      u <- liftIO getLine
      liftIO $ putStr "Account: "
      acc <- liftIO getLine
      send socket clr $ Left $ GetBalance u acc
      recv socket >>= \case
        Just lab -> unlabel lab >>= \case
          Right (Balance bal) -> liftIO $ print bal
          resp -> error $ "Unrecognized response: " ++ show resp
        Nothing -> error "Error recv'ing!"
      inSession socket
    "Create" -> do
      liftIO $ putStr "User: "
      u <- liftIO getLine
      send socket clr $ Left $ Create u
      recv socket >>= \case
        Just lab -> unlabel lab >>= \case
          Right Ack -> return ()
          resp -> error $ "Unrecognized response: " ++ show resp
        Nothing -> error "Error recv'ing!"
      inSession socket
    "Transfer" -> do
      liftIO $ putStr "From user: "
      uFrom <- liftIO getLine
      liftIO $ putStr "From account: "
      accFrom <- liftIO getLine
      liftIO $ putStr "To user: "
      uTo <- liftIO getLine
      liftIO $ putStr "To account: "
      accTo <- liftIO getLine
      liftIO $ putStr "Amount: "
      amount <- read <$> liftIO getLine
      send socket clr $ Left $ Transfer amount (uFrom, accFrom) (uTo, accTo)
      recv socket >>= \case
        Just lab -> unlabel lab >>= \case
          Right Ack -> return ()
          resp -> error $ "Unrecognized response: " ++ show resp
        Nothing -> error "Error recv'ing!"
      inSession socket
    "Open" -> do
      liftIO $ putStr "User: "
      u <- liftIO getLine
      liftIO $ putStr "Account: "
      acc <- liftIO getLine
      send socket clr $ Left $ OpenAccount u acc
      recv socket >>= \case
        Just lab -> unlabel lab >>= \case
          Right Ack -> return ()
          resp -> error $ "Unrecognized response: " ++ show resp
        Nothing -> error "Error recv'ing!"
      inSession socket
    "Close" -> do
      liftIO $ putStr "User: "
      u <- liftIO getLine
      liftIO $ putStr "Account: "
      acc <- liftIO getLine
      send socket clr $ Left $ CloseAccount u acc
      recv socket >>= \case
        Just lab -> unlabel lab >>= \case
          Right Ack -> return ()
          resp -> error $ "Unrecognized response: " ++ show resp
        Nothing -> error "Error recv'ing!"
      inSession socket
    "Exit" -> send socket clr $ Left $ EndSession
    _ -> inSession socket

prompt :: LSocket (Either Request Response) -> BankT FLAMIO ()
prompt socket = do
  Name clr <- getClearance
  send socket clr $ Left $ StartSession clr
  recv socket >>= \case
    Just lab -> unlabel lab >>= \case
      Right Ack -> return ()
      resp -> error $ "Unrecognized response: " ++ show resp
    Nothing -> error "Error recv'ing!"
  inSession socket
  
report :: String -> BankT FLAMIO ()
report s = liftIO $ putStrLn s

{-
example :: BankT FLAMIO ()
example = do
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled bot (("A" %), ("B" %))) . unH
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled bot (("BankServer" →), ("BankClient" →))) . unH
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled bot (("Mathias" ←), ("BankClient" ←))) . unH
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled bot (("Mathias" →), ("BankClient" →))) . unH
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled bot (("BankServer" →), ("BankClient" →))) . unH
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled bot (("BankClient" →), ("BankServer" →))) . unH
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled bot (("BankServer" →), ("Mathias" →))) . unH
  liftLIO $ modify $ over _2 $ H . Set.insert (Labeled ("BankClient" %) (("Mathias" →), ("BankServer" →))) . unH

  withStrategy [bot] $ do
    x <- ((⊤) ←) ≽ ("BankClient" ←)
    liftFLAMIO $ liftIO $ print x
-}

example :: BankT FLAMIO ()
example = do
  liftIO $ hSetBuffering stdout NoBuffering
  liftIO $ putStr "Client: "
  uClient <- liftIO getLine
  newScope $ do
    withStrategy [bot] $ do
      report "1"
      addDelegate ("BankServer" ←) ("BankClient" ←) bot
      report "1"
      addDelegate ("BankServer" →) ("BankClient" →) bot
      report "2"
      addDelegate (uClient ←) ("BankClient" ←) bot
      report "2"

      report "3"
      addDelegate (uClient →) ("BankClient" →) bot
      report "3"
      report "4"
      addDelegate ("BankClient" ←) (uClient ←) bot
      report "4"
      -- Now: BankClient ⊑ uClient
      
      connect ("127.0.0.1", "8000", "BankServer") $ \(socket :: LSocket (Either Request Response)) -> do
        report "5"
        sendDelegate socket ("BankServer" →) ("BankClient" →) bot
        report "5"
        report "6"
        recvDelegate socket >>= \case
          True -> do
            report "6"
            -- Now: BankServer ⊑ BankClient
            report "7"
            send socket "BankClient" (Left $ StartSession uClient)
            report "7"
            report "8"
            addDelegate ("BankServer" →) (uClient →) bot
            sendDelegate socket ("BankServer" →) (uClient →) bot
            report "8"
            report "9"
            recvDelegate socket >>= \case
              True -> do
                report "9"
                withStrategy [("BankClient" %) :: Principal] $ do
                  -- Now: BankServer ⊑ uClient
                  liftLIO $ modify $ _1 . clearance .~ (uClient %)
                  report "10"
                  recvDelegate socket >>= \case
                    True -> do
                      sendDelegate socket (uClient ←) ("BankClient" ←) uClient
                      report "10"
                      report "11"
                      recv socket >>= \case
                        Just lab -> do
                          report "11"
                          report "12"
                          unlabel lab >>= \case
                            Right Ack -> do
                              report "12"
                              inSession socket
                        Nothing -> error "Error recv'ing!"
              False -> error "Could not receive delegation"
          False -> error "Could not receive delegation"
        --recvDelegation socket (uClient ←) ("BankServer" ←)
        --prompt socket

main :: IO ()
main =
  evalStateT (unLIO (runFLAM (execBankT example Map.empty)))
  (BoundedLabel { _cur = bot, _clearance = ("BankClient" %) }, H Set.empty, noStrategy) >>= print
