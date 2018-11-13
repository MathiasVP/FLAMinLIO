{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, GeneralizedNewtypeDeriving, PostfixOperators #-}
module JukeBox where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import Data.Set(Set)
import Control.Monad.State
import Control.Monad.Catch
import GHC.Generics
import Control.Concurrent.Forkable
import Control.Lens
import Data.Ord

type User = Principal

type JukeBoxData = (Maybe String, Map String (Set (Labeled Principal Principal)))

newtype JukeBoxT m a = JukeBoxT { runJukeBoxT :: StateT (MVar JukeBoxData) m a }
  deriving (Functor, Applicative, Monad, MonadState (MVar JukeBoxData), MonadTrans)

evalJukeBoxT :: Monad m => JukeBoxT m a -> MVar JukeBoxData -> m a
evalJukeBoxT = evalStateT . runJukeBoxT

instance MonadLIO l m => MonadLIO l (JukeBoxT m) where
  liftLIO = JukeBoxT . liftLIO
  
instance MonadFLAMIO m => MonadFLAMIO (JukeBoxT m) where
  liftFLAMIO = JukeBoxT . liftFLAMIO

instance MonadIO m => MonadIO (JukeBoxT m) where
  liftIO = JukeBoxT . liftIO

instance MonadThrow m => MonadThrow (JukeBoxT m) where
  throwM = JukeBoxT . throwM

instance MonadCatch m => MonadCatch (JukeBoxT m) where
  catch (JukeBoxT m) f = JukeBoxT $ catch m (runJukeBoxT . f)

instance MonadMask m => MonadMask (JukeBoxT m) where
  mask a = JukeBoxT $ mask $ \u -> runJukeBoxT (a $ q u)
    where q u (JukeBoxT b) = JukeBoxT (u b)

  uninterruptibleMask a = JukeBoxT $ uninterruptibleMask $ \u -> runJukeBoxT (a $ q u)
    where q u (JukeBoxT b) = JukeBoxT (u b)

  generalBracket acquire release use = JukeBoxT $ generalBracket
    (runJukeBoxT acquire)
    (\resource exitCase -> runJukeBoxT (release resource exitCase))
    (\resource -> runJukeBoxT (use resource))

instance ForkableMonad m => ForkableMonad (JukeBoxT m) where
  forkIO (JukeBoxT m) = JukeBoxT $ forkIO m

vote :: MonadFLAMIO m => Labeled Principal String -> JukeBoxT m Bool
vote ls = do
  let p = labelOf ls
  lp <- label "J" p
  s <- unlabel ls
  mvar <- get
  (curSong, songs) <- liftFLAMIO $ liftIO $ takeMVar mvar
  let songs' = case Map.lookup s songs of
                 Just votes -> Map.insert s (Set.insert lp votes) songs
                 Nothing -> Map.insert s (Set.singleton lp) songs
  liftFLAMIO $ liftIO $ putMVar mvar (curSong, songs')
  return True

candidates :: MonadFLAMIO m =>
              JukeBoxT m (Map String (Set (Labeled Principal Principal)))
candidates = do
  mvar <- get
  (_, songs) <- liftFLAMIO $ liftIO $ readMVar mvar
  return songs

play :: MonadFLAMIO m => JukeBoxT m String
play = do
  mvar <- get
  (_, songs) <- liftFLAMIO $ liftIO $ takeMVar mvar
  let (song, _) = List.maximumBy (\(_, ps) (_, qs) -> compare (Set.size ps) (Set.size qs)) (Map.toList songs)
  liftFLAMIO $ liftIO $ putMVar mvar (Just song, Map.delete song songs)
  return song
