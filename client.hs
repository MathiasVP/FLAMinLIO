{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, PostfixOperators #-}

module Network where
import FLAM
import LIO
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import Control.Monad.State
import qualified Data.Set as Set

aliceSecret :: Labeled FLAM Bool
aliceSecret = Labeled { _labeledLab = Name "Alice", _labeledVal = True }

example :: FLAMIO ()
example = do
  connect ("127.0.0.1", "8000", "Server") $ \(socket :: LSocket (Labeled FLAM Bool)) -> do
    send socket aliceSecret
  return ()

runExample :: IO ()
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
