{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE GADTs #-}
module Lib.Network where

import Lib.FLAM
import Lib.LIO
import Lib.SendRecv
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Catch
import Control.Monad.Reader
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net
import Control.Lens.Tuple
import Control.Lens hiding ((:<))
import Control.Concurrent
import Data.Typeable
import Data.Binary
import Data.Dynamic.Binary

type IP = String
type Name = String
type Port = String
type Host a = (IP, Port, a, Port)

channelLabel :: LSocket a -> Principal
channelLabel (LSocket (_, s)) = s

waitForQuery :: Net.Socket -> Principal -> Principal -> MVar H -> IO ()
waitForQuery s lbl clr mvar = do
  catch (do
    h <- readMVar mvar
    recv s >>= \case
      Just (p :: Principal, q :: Principal, strat :: Strategy Principal) -> do
        (b, (BoundedLabel lbl' clr', _, _)) <- runStateT (runFLAM (p ≽ q)) (BoundedLabel lbl clr, h, strat)
        send s b
        waitForQuery s lbl' clr' mvar
      Nothing -> do
        send s False
        waitForQuery s lbl clr mvar)
    (\(e :: SomeException) -> return ())

serve :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocketRPC -> m r) -> m ()
serve (ip, port, name, fwdPort) f = do
  Net.listen (Net.Host ip) port (\(socket, addr) ->
    Net.accept socket (\(socket', _) -> do
      send socket' False -- Send dummy message to the client saying "I am now waiting on a connection for forward requests"
      Net.listen (Net.Host ip) fwdPort (\(fwdsocket, fwdaddr) ->
        Net.accept fwdsocket (\(fwdsocket', _) ->
          let lfwdsocket = LSocketRPC (fwdsocket', (%) name)
          in do putSocketRPC lfwdsocket
                h <- liftFLAMIO $ getHPtr
                lbl <- getLabel
                clr <- getClearance
                tid <- liftFLAMIO $ liftLIO $ liftIO $ forkIO (waitForQuery fwdsocket' lbl clr h)
                f (LSocketRPC (socket', (%) name))
                removeSocketRPC lfwdsocket
                liftFLAMIO $ liftLIO $ liftIO $ killThread tid))))
            
connect :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocketRPC -> m r) -> m ()
connect (ip, port, name, fwdPort) f = do
  Net.connect ip port (\(socket, _) -> do
    -- Wait for the server to say "I am now listening for a connection for doing forward requests"
    recv socket >>= \case
      Just (_ :: Bool) -> 
        Net.connect ip fwdPort (\(fwdsocket, _) ->
          let lfwdsocket = LSocketRPC (fwdsocket, (%) name)
          in do putSocketRPC lfwdsocket
                h <- liftFLAMIO $ getHPtr
                lbl <- getLabel
                clr <- getClearance
                tid <- liftFLAMIO $ liftLIO $ liftIO $ forkIO (waitForQuery fwdsocket lbl clr h)
                f (LSocketRPC (socket, (%) name))
                removeSocketRPC lfwdsocket
                liftFLAMIO $ liftLIO $ liftIO $ killThread tid
                send socket (Nothing :: Maybe (String, [Dynamic])))
      Nothing -> error "Could not establish connection for forward requests!")

instance MonadThrow m => MonadThrow (AssumptionsT m) where
  throwM = AssumptionsT . throwM
  
instance MonadCatch m => MonadCatch (AssumptionsT m) where
  catch (AssumptionsT m) f = AssumptionsT $ catch m (unAssumptionsT . f)
  
instance MonadMask m => MonadMask (AssumptionsT m) where
  mask a = AssumptionsT $ mask $ \u -> unAssumptionsT (a $ q u)
    where q u (AssumptionsT b) = AssumptionsT (u b)

  uninterruptibleMask a = AssumptionsT $ uninterruptibleMask $ \u -> unAssumptionsT (a $ q u)
    where q u (AssumptionsT b) = AssumptionsT (u b)

  generalBracket acquire release use = AssumptionsT $ generalBracket
    (unAssumptionsT acquire)
    (\resource exitCase -> unAssumptionsT (release resource exitCase))
    (\resource -> unAssumptionsT (use resource))
  
instance MonadThrow FLAMIO where
  throwM = FLAMIO . throwM

instance MonadCatch FLAMIO where
  catch (FLAMIO m) f = FLAMIO $ catch m (unFLAMIO . f)

instance MonadMask FLAMIO where
  mask a = FLAMIO $ mask $ \u -> unFLAMIO (a $ q u)
    where q u (FLAMIO b) = FLAMIO (u b)

  uninterruptibleMask a = FLAMIO $ uninterruptibleMask $ \u -> unFLAMIO (a $ q u)
    where q u (FLAMIO b) = FLAMIO (u b)

  generalBracket acquire release use = FLAMIO $ generalBracket
    (unFLAMIO acquire)
    (\resource exitCase -> unFLAMIO (release resource exitCase))
    (\resource -> unFLAMIO (use resource))  

instance MonadIO m => MonadIO (AssumptionsT m) where
  liftIO = AssumptionsT . liftIO

{- NOTE: This is a dangerous operation that should be put in a seperate (TCB) module! -}
instance MonadIO FLAMIO where
  liftIO = FLAMIO . liftIO
