{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module FileSystem where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map)
import Control.Monad.State hiding (modify')
import Control.Monad.Catch
import GHC.Generics
import Data.Maybe
import qualified Data.Binary as Bin
import Control.Concurrent.Forkable
import Control.Arrow
import Prelude hiding (Left, Right)

type FileName = String
type FolderName = String

data File a
  = Document FileName (Labeled Principal a)
  | Directory FolderName (Labeled Principal [File a])
  deriving Generic

data Direction = Up | Down | Left | Right

nameOfFile :: File a -> String
nameOfFile (Document name _) = name
nameOfFile (Directory name _) = name

type Path = [Direction]

instance Bin.Binary a => Bin.Binary (File a)

instance Show a => Show (File a) where
  show (Document s _) = "Document: " ++ s
  show (Directory s _) = "Directory: " ++ s

newtype FileSystemT a m b = FileSystemT { runFileSystemT :: StateT (MVar (File a), Path) m b }
  deriving (Functor, Applicative, Monad, MonadState (MVar (File a), Path), MonadTrans)

instance MonadLIO l m => MonadLIO l (FileSystemT a m) where
  liftLIO = FileSystemT . liftLIO
  
instance MonadFLAMIO m => MonadFLAMIO (FileSystemT a m) where
  liftFLAMIO = FileSystemT . liftFLAMIO

instance MonadIO m => MonadIO (FileSystemT a m) where
  liftIO = FileSystemT . liftIO

instance MonadThrow m => MonadThrow (FileSystemT a m) where
  throwM = FileSystemT . throwM

instance MonadCatch m => MonadCatch (FileSystemT a m) where
  catch (FileSystemT m) f = FileSystemT $ catch m (runFileSystemT . f)

instance MonadMask m => MonadMask (FileSystemT a m) where
  mask a = FileSystemT $ mask $ \u -> runFileSystemT (a $ q u)
    where q u (FileSystemT b) = FileSystemT (u b)

  uninterruptibleMask a = FileSystemT $ uninterruptibleMask $ \u -> runFileSystemT (a $ q u)
    where q u (FileSystemT b) = FileSystemT (u b)

  generalBracket acquire release use = FileSystemT $ generalBracket
    (runFileSystemT acquire)
    (\resource exitCase -> runFileSystemT (release resource exitCase))
    (\resource -> runFileSystemT (use resource))

instance MonadFix m => MonadFix (FileSystemT a m) where
  mfix f = FileSystemT $ mfix $ \a -> runFileSystemT (f a)
  
instance (ForkableMonad m) => ForkableMonad (FileSystemT a m) where
  forkIO (FileSystemT m) = FileSystemT $ forkIO m

evalFileSystemT :: (Monad m, MonadIO m) => FileSystemT a m b -> MVar (File a) -> m b
evalFileSystemT fs mvar = evalStateT (runFileSystemT fs) (mvar, [])

modifyM :: MonadState s m => (s -> m s) -> m ()
modifyM f = get >>= (f >=> put)

getsM :: MonadState s m => (s -> m a) -> m a
getsM f = get >>= f

modifyM' :: MonadState s m => (s -> m (s, a)) -> m a
modifyM' f = do
  (s', a) <- get >>= f
  put s'
  return a

modify' :: MonadState s m => (s -> (s, a)) -> m a
modify' f = do
  (s', a) <- f <$> get
  put s'
  return a

follow' :: Path -> Maybe (File a) -> [File a] -> [File a] ->
          [(Maybe (File a), [File a], [File a])] -> FileSystemT a FLAMIO (Maybe (File a))
follow' (Up : path) _ leftOf rightOf ((mfile, leftOf', rightOf') : ups) =
  follow' path mfile leftOf' rightOf' ups
follow' (Down : path) (Just (Directory name content)) leftOf rightOf ups = do
  content' <- unlabel content
  case content' of
    file : files -> follow' path (Just file) [] files ((Just (Directory name content), leftOf, rightOf) : ups)
    [] -> follow' path Nothing [] [] ((Just (Directory name content), leftOf, rightOf) : ups)
follow' (Left : path) mfile (file : leftOf) rightOf ups = do
  let rightOf' = maybeToList mfile ++ rightOf
  follow' path (Just file) leftOf rightOf' ups
follow' (Left : path) mfile leftOf (file : rightOf) ups = do
  let leftOf' = maybeToList mfile ++ leftOf
  follow' path (Just file) leftOf' rightOf ups

follow :: Path -> File a -> FileSystemT a FLAMIO (Maybe (File a))
follow path file = follow' path (Just file) [] [] []

addDirection :: Direction -> FileSystemT a FLAMIO Bool
addDirection dir = do
  (mvar, path) <- get
  file <- liftIO $ readMVar mvar 
  follow (path ++ [dir]) file >>= \case
    Just _ -> do
      put (mvar, path ++ [Down])
      return True
    Nothing -> return False
  
down :: () -> FileSystemT a FLAMIO Bool
down () = addDirection Down

up :: () -> FileSystemT a FLAMIO Bool
up () = addDirection Up

left :: () -> FileSystemT a FLAMIO Bool
left () = addDirection Left

right :: () -> FileSystemT a FLAMIO Bool
right () = addDirection Right

ls :: () -> FileSystemT a FLAMIO (Maybe (File a))
ls () = do
  (mvar, path) <- get
  file <- liftIO $ readMVar mvar
  follow path file

{-
cat :: () -> FileSystemT a FLAMIO (Maybe a)
cat () = getsM $ \mvar -> do
           (f, _) <- liftIO $ readMVar mvar
           case f of
             Just (Document _ lc) -> Just <$> unlabel lc
             _ -> return Nothing

write :: a -> FileSystemT a FLAMIO Bool
write a = do
  modifyM' $ \mvar -> do
    (file, path) <- liftIO $ takeMVar mvar
    case file of
      Just (Directory {}) -> do
        liftIO $ putMVar mvar (file, path)
        return (mvar, False)
      Just (Root {}) -> do
        liftIO $ putMVar mvar (file, path)
        return (mvar, False)
      Just (Document s d) -> do
        a' <- label (labelOf d) a
        liftIO $ putMVar mvar (Just (Document s a'), path) 
        return (mvar, True)
      _ -> do
        liftIO $ putMVar mvar (file, path)
        return (mvar, False)

append :: Monoid a => a -> FileSystemT a FLAMIO Bool
append b =
  cat () >>= \case
    Just a -> write (a <> b)
    Nothing -> return False

touch :: (ToLabel q Principal, Monoid a) => q -> FileName -> FileSystemT a FLAMIO Bool
touch q s = do
  modifyM' $ \(mvar, path) -> do
    liftIO (takeMVar mvar) >>= \case
      Directory name content -> do
        content <- label q mempty
        liftIO $ putMVar mvar (Just (Document s content), (msp, maybeToList file ++ fs1, fs2):path) 
        return (mvar, True)

mkdir :: (ToLabel q Principal, Monoid a) => q -> FileName -> FileSystemT a FLAMIO Bool
mkdir q s = do
  modifyM' $ \mvar -> do
    liftIO (takeMVar mvar) >>= \case
      (file, (msp, fs1, fs2):path) -> do
        content <- label q []
        liftIO $ putMVar mvar (Just (Directory s content), (msp, maybeToList file ++ fs1, fs2):path)
        return (mvar, True)
      (mfile, path) -> do
        liftIO $ putMVar mvar (mfile, path)
        return (mvar, False)
-}
