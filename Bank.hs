{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE LambdaCase #-}
module Bank where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.ByteString as B
import Control.Monad.State
import Control.Monad.Catch
import GHC.Generics
import qualified Data.Binary as Bin
import Control.Concurrent.Forkable

type BankData = Map String (Labeled Principal Int)

newtype BankT m a = BankT { runBankT :: StateT (MVar BankData) m a }
  deriving (Functor, Applicative, Monad, MonadState (MVar BankData), MonadTrans)

instance MonadLIO l m => MonadLIO l (BankT m) where
  liftLIO = BankT . liftLIO
  
instance MonadFLAMIO m => MonadFLAMIO (BankT m) where
  liftFLAMIO = BankT . liftFLAMIO

instance MonadIO m => MonadIO (BankT m) where
  liftIO = BankT . liftIO

instance MonadThrow m => MonadThrow (BankT m) where
  throwM = BankT . throwM

instance MonadCatch m => MonadCatch (BankT m) where
  catch (BankT m) f = BankT $ catch m (runBankT . f)

instance MonadMask m => MonadMask (BankT m) where
  mask a = BankT $ mask $ \u -> runBankT (a $ q u)
    where q u (BankT b) = BankT (u b)

  uninterruptibleMask a = BankT $ uninterruptibleMask $ \u -> runBankT (a $ q u)
    where q u (BankT b) = BankT (u b)

  generalBracket acquire release use = BankT $ generalBracket
    (runBankT acquire)
    (\resource exitCase -> runBankT (release resource exitCase))
    (\resource -> runBankT (use resource))

instance ForkableMonad m => ForkableMonad (BankT m) where
  forkIO (BankT m) = BankT $ forkIO m
  
execBankT :: MonadIO m => BankT m a -> MVar BankData -> m BankData
execBankT m mvar = do
  _ <- runStateT (runBankT m) mvar
  liftIO $ readMVar mvar

login :: MonadFLAMIO m => String -> String -> BankT m (Labeled Principal Principal)
login u p =
  if p == "password" then label ("B" ←) (u %) else label ("B" ←) (⊥)

balance :: MonadFLAMIO m => Labeled Principal Principal -> String -> BankT m (Maybe Int)
balance tok s = do
  u <- unlabel tok
  u ≽ s >>= \case
    False -> return Nothing
    True -> do
      b <- get >>= liftFLAMIO . liftIO . readMVar
      case Map.lookup s b of
        Just ln -> do
          n <- unlabel ln
          return $ Just n
        Nothing -> return Nothing

transfer :: MonadFLAMIO m => Labeled Principal Principal -> String -> String -> Int -> BankT m Bool
transfer tok sFrom sTo n = do
  u <- unlabel tok
  u ≽ sFrom >>= \case
    False -> return False
    True -> do
      mvar <- get
      b <- liftFLAMIO $ liftIO $ readMVar mvar
      case Map.lookup sFrom b of
        Just lnFrom -> do
          nFrom <- unlabel lnFrom
          if nFrom >= n then
            case Map.lookup sTo b of
              Just lnTo -> do
                clr <- getClearance
                toLabeled clr $ do
                  nTo <- unlabel lnTo
                  lnTo' <- newScope $ do
                             lbl <- getLabel
                             addDelegate (sTo →) ("B" →) lbl
                             label sTo (nTo + n)
                  liftFLAMIO $ liftIO $ putMVar mvar $
                    Map.insert sTo lnTo' b

                toLabeled clr $ do
                  b' <- liftFLAMIO $ liftIO $ readMVar mvar
                  lnFrom' <- label sFrom (nFrom - n)
                  liftFLAMIO $ liftIO $ putMVar mvar $
                    Map.insert sFrom lnFrom' b'
                return True
          else return False
        Nothing -> return False
