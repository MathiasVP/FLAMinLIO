{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

type User = String
type Account = String
type Balance = Int
type BankData = Map User (Labeled Principal (Map Account Balance))

newtype BankT m a = BankT { runBankT :: StateT BankData m a }
  deriving (Functor, Applicative, Monad, MonadState BankData, MonadTrans)

instance MonadLIO s l m => MonadLIO s l (BankT m) where
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

execBankT :: Monad m => BankT m a -> BankData -> m BankData
execBankT = execStateT . runBankT

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

data Request
  = GetBalance User Account
  | Transfer Int (User, Account) (User, Account)
  | OpenAccount User Account
  | CloseAccount User Account
  | StartSession User
  | EndSession
  | Create User
  deriving (Show, Generic)

instance Bin.Binary Request

data Response
  = Ack
  | Balance Int
  | NoSuchAccount
  | NoSuchUser
  | NonEmptyAccount
  | ProtocolError
  | NotSufficientFunds
  | UserAlreadyExists
  deriving (Show, Generic)

instance Bin.Binary Response
