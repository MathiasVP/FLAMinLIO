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
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Catch
import Control.Monad.Reader
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net
import Control.Lens.Tuple
import Data.Tuple.Only
import Control.Lens hiding ((:<))
import Data.Typeable

type IP = String
type Name = String
type Port = String
type Host a = (IP, Port, a)

channelLabel :: LSocket a -> Principal
channelLabel (LSocket (_, s)) = s

serve :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocket a -> m r) -> m ()
serve (ip, port, name) f = do
  Net.listen (Net.Host ip) port (\(socket, addr) -> Net.accept socket (\(socket', _) -> f (LSocket (socket', (%) name))))
  return ()
  
connect :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocket a -> m r) -> m ()
connect (ip, port, name) f = do
  Net.connect ip port (\(socket, _) -> f (LSocket (socket, (%) name)))
  return ()

serveRPC :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocketRPC -> m r) -> m ()
serveRPC (ip, port, name) f = do
  Net.listen (Net.Host ip) port (\(socket, addr) ->
    Net.accept socket (\(socket', _) ->
      let lsocket = LSocketRPC (socket', (%) name)
      in putSocketRPC lsocket >> f lsocket >> removeSocketRPC lsocket))
  return ()
  
connectRPC :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocketRPC -> m r) -> m ()
connectRPC (ip, port, name) f = do
  Net.connect ip port (\(socket, _) ->
    let lsocket = LSocketRPC (socket, (%) name)
    in putSocketRPC lsocket >> f lsocket >> removeSocketRPC lsocket)
  return ()

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
