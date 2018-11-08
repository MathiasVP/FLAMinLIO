{-# LANGUAGE TupleSections #-}
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
import Data.Map(Map)
import qualified Data.Set as Set
import Algebra.Lattice.Op
import Algebra.PartialOrd
import Data.Maybe
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
import Data.Typeable
import Data.Binary
import Control.Concurrent.Forkable
import Data.Dynamic.Binary
import qualified Network.Socket as NS
import Data.Bits (shiftR, (.&.))
import Data.POMap.Strict(POMap)
import Data.POMap.Internal(chainDecomposition, mkPOMap)

type Name = String
type ServeHost a = (IP, Port, a, Port)
type ConHost a = (IP, Port, a, Port)

waitForQuery :: Net.Socket -> Principal -> Principal -> MVar H -> MVar [LSocketRPC] -> IO ()
waitForQuery s lbl clr mvarH mvarSocks = do
  catch (do
    recv s >>= \case
      Just (p :: Principal, q :: Principal, strat :: Strategy Principal, others :: [Principal]{-, bcache :: BinaryableCache-}) -> do
        (b, (BoundedLabel lbl' clr', _)) <-
          runStateT (runFLAM (noForwardTo (Set.fromList others) (p ≽ q)) mvarH mvarSocks) (BoundedLabel lbl clr, strat)
        send s b
        waitForQuery s lbl' clr' mvarH mvarSocks
      Nothing -> do
        send s False
        waitForQuery s lbl clr mvarH mvarSocks)
    (\(e :: SomeException) -> return ())

-- TODO: These really shouldn't be here. They're pulled from network-simple's internal and tcp files,
-- and generalized slighly from IO to any forkable monad. We should probably do a pull request to fix this.
ipv4mapped_to_ipv4:: NS.SockAddr -> NS.SockAddr
ipv4mapped_to_ipv4 (NS.SockAddrInet6 p _ (0, 0, 0xFFFF, h) _)
  = NS.SockAddrInet p (NS.tupleToHostAddress
      (fromIntegral (shiftR (h .&. 0xFF000000) 24),
       fromIntegral (shiftR (h .&. 0x00FF0000) 16),
       fromIntegral (shiftR (h .&. 0x0000FF00) 8),
       fromIntegral         (h .&. 0x000000FF)))
ipv4mapped_to_ipv4 sa = sa

acceptFork
  :: (MonadIO m, MonadMask m, ForkableMonad m)
  => NS.Socket
  -> ((NS.Socket, NS.SockAddr) -> m ())
  -> m ThreadId
acceptFork lsock k = mask $ \restore -> do
  (csock, addr) <- restore (liftIO $ NS.accept lsock)
  onException
     (forkIO (finally (restore (k (csock, ipv4mapped_to_ipv4 addr)))
                         (Net.closeSock csock)))
     (Net.closeSock csock)

serve :: (MonadIO m, ForkableMonad m, MonadMask m, MonadFLAMIO m) => IP -> Port -> Port -> (LSocketRPC -> m r) -> m ()
serve ip port fwdPort f = do
  mvar <- liftIO $ newEmptyMVar
  done <- liftIO $ newEmptyMVar
  forkIO $ do
    Net.listen (Net.Host ip) port (\(socket, _) -> do
      forever $ do
        acceptFork socket (\(socket', _) -> do
          liftIO $ putMVar mvar socket'
          liftIO $ takeMVar done))
  Net.listen (Net.Host ip) fwdPort (\(fwdSocket, _) -> do
    forever $ do
      socket' <- liftIO $ takeMVar mvar
      send socket' False -- Send dummy message to the client saying "I am now waiting on a connection for forward requests"
      acceptFork fwdSocket (\(fwdsocket', _) -> do
        clientPrinc <- recv socket' >>= \case
            Just (p :: Principal) -> return p
            Nothing -> error "Did not receive name of client!"
        clr <- liftFLAMIO getClearance
        send socket' clr
        let lfwdsocket = LSocketRPC (fwdsocket', clientPrinc)
        putSocketRPC lfwdsocket
        h <- liftFLAMIO $ getHPtr
        socks <- liftFLAMIO $ getSocketsRPC
        lbl <- getLabel
        clr <- getClearance
        tid <- liftFLAMIO $ liftLIO $ liftIO $ forkIO (waitForQuery fwdsocket' lbl clr h socks)
        f (LSocketRPC (socket', clientPrinc))
        removeSocketRPC lfwdsocket
        liftFLAMIO $ liftLIO $ liftIO $ killThread tid
        liftIO $ putMVar done ()))
 
connect :: (ForkableMonad m, MonadIO m, MonadMask m, MonadFLAMIO m) => IP -> Port -> Port -> (LSocketRPC -> m r) -> m ()
connect ip port fwdPort f = do
  Net.connect ip port (\(socket, _) -> do
    -- Wait for the server to say "I am now listening for a connection for doing forward requests"
    recv socket >>= \case
      Just (_ :: Bool) -> 
        Net.connect ip fwdPort (\(fwdsocket, _) -> do
          clr <- liftFLAMIO getClearance
          send socket clr
          serverPrinc <- recv socket >>= \case
            Just (p :: Principal) -> return p
            Nothing -> error "Did not receive name of server!"
          let lfwdsocket = LSocketRPC (fwdsocket, serverPrinc)
          putSocketRPC lfwdsocket
          h <- liftFLAMIO getHPtr
          socks <- liftFLAMIO getSocketsRPC
          lbl <- getLabel
          clr <- getClearance
          tid <- liftFLAMIO $ liftLIO $ liftIO $ forkIO (waitForQuery fwdsocket lbl clr h socks)
          f (LSocketRPC (socket, serverPrinc))
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

{- NOTE: This is a dangerous operation that should be put in a seperate (TCB) module! -}
instance MonadIO FLAMIO where
  liftIO = FLAMIO . liftIO
