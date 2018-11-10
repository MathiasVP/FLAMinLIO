{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module JukeBoxServer where

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
import JukeBox
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

example :: JukeBoxT FLAMIO ()
example = do
  export "vote"       $ exportable1 (vote :: Labeled Principal String -> JukeBoxT FLAMIO Bool)
  export "candidates" $ exportable1 (const candidates :: Int ->
                          JukeBoxT FLAMIO (Map String (Set (Labeled Principal Principal))))
  export "play"       $ exportable1 (const play :: Int -> JukeBoxT FLAMIO Bool)
  
  serve "127.0.0.1" "8000" $ \socket -> do
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
  st <- newMVar (Nothing, Map.empty)
  runFLAM "J" $ evalJukeBoxT example st





