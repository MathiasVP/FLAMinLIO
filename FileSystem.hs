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

type FileName = String
type FolderName = String

data File a
  = Document FileName (Labeled Principal a)
  | Directory FolderName (Labeled Principal [File a])
  | Root [File a]
  deriving Generic

type Path a = (Maybe (String, Principal), [File a], [File a])

type FileSystem a = (Maybe (File a), [Path a])

instance Bin.Binary a => Bin.Binary (File a)

instance Show a => Show (File a) where
  show (Document s _) = "Document: " ++ s
  show (Directory s _) = "Directory: " ++ s
  show (Root _) = "Root"
  

newtype FileSystemT b m a = FileSystemT { runFileSystemT :: StateT (FileSystem b) m a }
  deriving (Functor, Applicative, Monad, MonadState (FileSystem b), MonadTrans)

instance MonadLIO s l m => MonadLIO s l (FileSystemT a m) where
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

evalFileSystemT :: Monad m => FileSystemT a m b -> m b
evalFileSystemT fs = evalStateT (runFileSystemT fs) (Nothing, [(Nothing, [], [])])

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

up :: () -> FileSystemT a FLAMIO Bool
up () =
  modifyM' $ \(file, path) -> do
    case path of
      (Just (s, p), fs1, fs2):path -> do
        fs <- label p (fs1 ++ maybeToList file ++ fs2)
        return ((Just (Directory s fs), path), True)
      (Nothing, fs1, fs2):path -> do
        let fs = fs1 ++ maybeToList file ++ fs2
        return ((Just (Root fs), path), True)
      _ -> return ((file, path), False)

left :: () -> FileSystemT a FLAMIO Bool
left () =
  modify' $ \(file, path) ->
    case path of
      (msp, f:fs1, fs2):path ->
        ((Just f, (msp, fs1, maybeToList file ++ fs2):path), True)
      _ -> ((file, path), False)

right :: () -> FileSystemT a FLAMIO Bool
right () =
  modify' $ \(file, path) ->
  case path of
    (msp, fs1, f:fs2):path ->
      ((Just f, (msp, maybeToList file ++ fs1, fs2):path), True)
    _ -> ((file, path), False)

down :: () -> FileSystemT a FLAMIO Bool
down () = do
  modifyM' $ \(file, path) ->
    case file of
      Just (Document {}) -> return ((file, path), False)
      Just (Directory s fs) -> do
        fs' <- unlabel fs
        case fs' of
          [] -> return ((Nothing, (Just (s, labelOf fs), [], fs'):path), True)
          f:fs'' -> return ((Just f, (Just (s, labelOf fs), [], fs''):path), True)
      Just (Root fs) ->
        case fs of
          [] -> return ((Nothing, (Nothing, [], fs):path), True)
          f:fs' -> return ((Just f, (Nothing, [], fs'):path), True)

ls :: () -> FileSystemT a FLAMIO (Maybe (File a))
ls () = gets fst

cat :: () -> FileSystemT a FLAMIO (Maybe a)
cat () = getsM $ \(f, _) ->
                case f of
                  Just (Document _ lc) -> Just <$> unlabel lc
                  _ -> return Nothing

write :: a -> FileSystemT a FLAMIO Bool
write a =
  modifyM' $ \(file, path) ->
  case file of
    Just (Directory {}) -> return ((file, path), False)
    Just (Root {}) -> return ((file, path), False)
    Just (Document s d) -> do
      a' <- label (labelOf d) a
      return ((Just (Document s a'), path), True)
    _ -> return ((file, path), False)

append :: Monoid a => a -> FileSystemT a FLAMIO Bool
append b =
  cat () >>= \case
    Just a -> write (a <> b)
    Nothing -> return False

touch :: (ToLabel q Principal, Monoid a) => q -> FileName -> FileSystemT a FLAMIO Bool
touch q s = do
  modifyM' $ \case
    (file, (msp, fs1, fs2):path) -> do
      content <- label q mempty
      return ((Just (Document s content), (msp, maybeToList file ++ fs1, fs2):path), True)
    (mfile, path) -> return ((mfile, path), False)

mkdir :: (ToLabel q Principal, Monoid a) => q -> FileName -> FileSystemT a FLAMIO Bool
mkdir q s = do
  modifyM' $ \case
    (file, (msp, fs1, fs2):path) -> do
      content <- label q []
      return ((Just (Directory s content), (msp, maybeToList file ++ fs1, fs2):path), True)
    (mfile, path) -> return ((mfile, path), False)
