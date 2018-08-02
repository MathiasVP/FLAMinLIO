{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module RPCExampleServer where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Map as Map
import Control.Lens
import Bank
import Data.Typeable
import Data.Dynamic.Binary

getBalance :: User -> Account -> BankT FLAMIO Response
getBalance u a =
  Map.lookup u <$> get >>= \case
    Just lacc ->
      Map.lookup a <$> unlabel lacc >>= \case
        Just bal -> return $ Balance bal
        Nothing -> return $ NoSuchAccount
    Nothing -> return $ NoSuchUser

create :: User -> BankT FLAMIO Response
create u =
  Map.lookup u <$> get >>= \case
    Just _ -> return UserAlreadyExists
    Nothing -> do
      lacc <- label u Map.empty
      modify $ Map.insert u lacc
      return Ack

open :: User -> Account -> BankT FLAMIO Response
open u a =
  Map.lookup u <$> get >>= \case
    Just lacc -> do
      acc <- unlabel lacc
      lacc' <- label u (Map.insert a 100 acc)
      modify $ Map.insert u lacc'
      return Ack
    Nothing -> return NoSuchUser

transfer :: User -> Account -> User -> Account -> Int -> BankT FLAMIO Response
transfer uFrom aFrom uTo aTo n = do
  Map.lookup uFrom <$> get >>= \case
    Just laccFrom -> do
      accFrom <- unlabel laccFrom
      case Map.lookup aFrom accFrom of
        Just balFrom
          | balFrom >= n -> do
              Map.lookup uTo <$> get >>= \case
                Just laccTo -> do
                  clr <- getClearance
                  toLabeled clr $ do
                    accTo <- unlabel laccTo
                    accTo' <- label uTo $ Map.update (Just . (+ n)) aTo accTo
                    modify $ Map.insert uTo accTo'
                  toLabeled clr $ do
                    accFrom' <- label uFrom $ Map.update (Just . (subtract n)) aFrom accFrom
                    modify $ Map.insert uFrom accFrom'
                  return Ack
                Nothing -> return NoSuchAccount
          | otherwise -> return NotSufficientFunds
        Nothing -> return NoSuchAccount
    Nothing -> return NoSuchUser

repeatUntilM :: Monad m => m Bool -> m ()
repeatUntilM m =
  m >>= \case
    True -> repeatUntilM m
    False -> return ()

example :: BankT FLAMIO ()
example = do
  toLabeled top $ do
    create "Chloe"
    open "Chloe" "Checking"

  addDelegate ("Mathias" ←) ("Chloe" ←) bot
  
  export "getBalance" (exportable2 getBalance)
  export "create" (exportable1 create)
  export "open" (exportable2 open)
  export "transfer" (exportable5 transfer)

  forever $ do
    serve ("127.0.0.1", "8000", (⊤), "8001") $ \socket -> do
      toLabeled top $
        repeatUntilM $ do
          withStrategy [top] $ do
            recvRPC socket >>= \case
              Just (Just (s, args)) -> do
                lookupRPC s >>= \case
                  Just g -> invoke g args >>= sendRPCResult socket >> return True
                  Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic) >> return True
              Just Nothing -> return False
              Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic) >> return True

main :: IO ()
main =
  evalStateT (runFLAM $ evalStateT (runBankT example) Map.empty)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
