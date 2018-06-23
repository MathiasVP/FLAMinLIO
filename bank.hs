{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Bank where

import Lib.FLAM
import Lib.LIO
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.ByteString as B
import Control.Monad.State
import Control.Monad.Catch

type User = String
type Account = String
type Balance = Int
type BankData = Map User (Labeled Principal (Map Account Balance))

newtype BankT m a = BankT { runBankT :: StateT BankData m a }
  deriving (Functor, Applicative, Monad, MonadState BankData)

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

instance Serializable Request where
  encode (GetBalance u a) = B.cons 0 (encode (u, a))
  encode (Transfer n (u1, a1) (u2, a2)) = B.cons 1 (encode (n, (u1, a1), (u2, a2)))
  encode (OpenAccount u a) = B.cons 2 (encode (u, a))
  encode (CloseAccount u a) = B.cons 3 (encode (u, a))
  encode (StartSession u) = B.cons 4 (encode u)
  encode EndSession = B.singleton 5

  decode bs =
    case B.uncons bs of
      Just (0, bs') -> uncurry GetBalance <$> decode bs'
      Just (1, bs') -> uncurry3 Transfer <$> decode bs'
      Just (2, bs') -> uncurry OpenAccount <$> decode bs'
      Just (3, bs') -> uncurry CloseAccount <$> decode bs'
      Just (4, bs') -> StartSession <$> decode bs'
      Just (5, bs') | bs' == B.empty -> Just EndSession
      _ -> Nothing

  maxSize _ = 1 + maxSize (undefined :: Int) + 2 * maxSize (undefined :: (User, Account))

data Response
  = Ack
  | Balance Int
  | NoSuchAccount
  | NoSuchUser
  | NonEmptyAccount
  | ProtocolError
  | NotSufficientFunds

instance Serializable Response where
  encode Ack = B.singleton 0 
  encode (Balance n) = B.cons 1 (encode n)
  encode NoSuchAccount = B.singleton 2
  encode NoSuchUser = B.singleton 3
  encode NonEmptyAccount = B.singleton 4
  encode ProtocolError = B.singleton 5
  encode NotSufficientFunds = B.singleton 6
  
  decode bs =
    case B.uncons bs of
      Just (0, bs') | bs' == B.empty -> Just Ack
      Just (1, bs') -> Balance <$> decode bs'
      Just (2, bs') | bs' == B.empty -> Just NoSuchAccount
      Just (3, bs') | bs' == B.empty -> Just NoSuchUser
      Just (4, bs') | bs' == B.empty -> Just NonEmptyAccount
      Just (5, bs') | bs' == B.empty -> Just ProtocolError
      Just (6, bs') | bs' == B.empty -> Just NotSufficientFunds
      _ -> Nothing

  maxSize _ = 1 + maxSize (undefined :: Int)
