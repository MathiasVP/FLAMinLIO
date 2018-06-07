{-# LANGUAGE ScopedTypeVariables #-}

module Network where
import FLAM
import LIO
import Data.ByteString.Char8 as B
import Text.Read as R
import Control.Monad.State
import qualified Data.Set as Set

instance Serializable Int where
  encode = B.pack . show
  decode = R.readMaybe . B.unpack
  maxSize _ = 32

example :: FLAMIO ()
example = serve ("127.0.0.1", "8000", "Alice") $ \(socket :: LSocket Int) -> do
  x <- recv socket
  liftLIO $ LIO $ StateT $ \s -> do
    print x
    return ((), s)
  let Labeled name (Just val) = x
  send socket (val + 1)
  return ()

runExample :: IO ()
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
