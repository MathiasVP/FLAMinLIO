{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module BankServer where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Set(Set)
import Bank
import Data.Typeable
import Data.Dynamic.Binary
import Prelude hiding (read)
import Control.Concurrent.MVar (newMVar)
import Control.Lens

repeatUntilM :: Monad m => m Bool -> m ()
repeatUntilM m =
  m >>= \case
    True -> repeatUntilM m
    False -> return ()

example :: BankT FLAMIO ()
example = do
  export "login"   $ exportable2 (login :: String -> String -> BankT FLAMIO (Labeled Principal Principal))
  export "balance" $ exportable2 (balance :: Labeled Principal Principal -> String ->
                                             BankT FLAMIO (Maybe Int))
  export "transfer" $ exportable4 (transfer :: Labeled Principal Principal -> String -> String -> Int -> BankT FLAMIO Bool)
  
  serve "127.0.0.1" "8000" $ \socket ->
    forever $
      toLabeled top $
        repeatUntilM $
          withStrategy [top] $
            recvRPC socket >>= \case
              Just (Just (s, args)) ->
                lookupRPC s >>= \case
                  Just g -> invoke g args >>= sendRPCResult socket >> return True
                  Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic) >> return True
              Just Nothing -> return False
              Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic) >> return True

main :: IO ()
main = do
  st <- newMVar (Map.fromList [("Alice", Labeled ("Alice" →) 50),
                               ("Bob", Labeled ("Bob" →) 50)])
  b <- runFLAM "B" $ execBankT example st
  return ()
