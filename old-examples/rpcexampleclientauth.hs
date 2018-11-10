{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module RPCExampleClient where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Lens
import Bank
import Data.Dynamic.Binary
import Data.Binary
import Control.Concurrent.MVar

example :: FLAMIO ()
example = do
  connect "127.0.0.1" "8000" "8001" $ \socket -> do
    newScope $ do
      withStrategy [bot] $ do
        addDelegate ("Chloe" ←) ("Mathias" ←) bot
        addDelegate ("Chloe" →) ("Mathias" →) bot
        liftIO getLine
        return ()

main :: IO ()
main = do
  h <- newMVar (H Set.empty)
  socks <- newMVar []
  evalStateT (runFLAM example h socks)
    (BoundedLabel { _cur = bot, _clearance = ("Freksen" %) }, noStrategy)
