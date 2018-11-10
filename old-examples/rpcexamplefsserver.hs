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
import FileSystem
import Data.Typeable
import Data.Dynamic.Binary
import Prelude hiding (read)
import Control.Concurrent.MVar (newMVar, isEmptyMVar)

repeatUntilM :: Monad m => m Bool -> m ()
repeatUntilM m =
  m >>= \case
    True -> repeatUntilM m
    False -> return ()

example :: FileSystemT String FLAMIO ()
example = do
  export "up" (exportable1 (up :: () -> FileSystemT String FLAMIO Bool))
  export "down" (exportable1 (down :: () -> FileSystemT String FLAMIO Bool))
  export "left" (exportable1 (left :: () -> FileSystemT String FLAMIO Bool))
  export "right" (exportable1 (right :: () -> FileSystemT String FLAMIO Bool))
  export "ls" (exportable1 (ls :: () -> FileSystemT String FLAMIO (Maybe (File String))))
  --export "cat" (exportable1 (cat :: () -> FileSystemT String FLAMIO (Maybe String)))
  --export "touch" (exportable2 (touch :: Principal -> FileName -> FileSystemT String FLAMIO Bool))
  --export "mkdir" (exportable2 (mkdir :: Principal -> FileName -> FileSystemT String FLAMIO Bool))
  --export "write" (exportable1 (write :: String -> FileSystemT String FLAMIO Bool))
  --export "append" (exportable1 (append :: String -> FileSystemT String FLAMIO Bool))
  
  serve ("127.0.0.1", "8000", (⊤), "8001") $ \socket -> do
    forever $
      toLabeled top $
        repeatUntilM $
          withStrategy [top] $ do
            recvRPC socket >>= \case
              Just (Just (s, args)) ->
                lookupRPC s >>= \case
                  Just g -> invoke g args >>= sendRPCResult socket >> return True
                  Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic) >> return True
              Just Nothing -> return False
              Nothing -> sendRPCResult socket (Nothing :: Maybe Dynamic) >> return True

main :: IO ()
main = do
  fs <- newMVar (Nothing, [(Nothing, [], [])])
  evalStateT (runFLAM $ evalFileSystemT example fs)
    (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, noStrategy)
