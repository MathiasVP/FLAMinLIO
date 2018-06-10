{-# LANGUAGE ScopedTypeVariables #-}

module Network where
import FLAM
import LIO
import Text.Read as R
import Control.Monad.State
import qualified Data.Set as Set

example :: FLAMIO ()
example = do
  x <- serve ("127.0.0.1", "8000", "Client") $ \(socket :: LSocket (Labeled FLAM Bool)) -> do
         recv socket
  liftLIO $ LIO $ StateT $ \s -> do
    print x
    return ((), s)

runExample :: IO ()
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
