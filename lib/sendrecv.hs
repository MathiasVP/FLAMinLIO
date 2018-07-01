{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PostfixOperators #-}
module Lib.SendRecv where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Catch
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net
import Control.Lens.Tuple
import Control.Lens hiding ((:<))

send :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel c Principal) => LSocket a -> c -> a -> m ()
send (LSocket (s, name)) me a = do
  lab <- liftLIO $ gets $ view _1
  b <- view cur lab ⊑ name
  unless b $
    fail ("IFC violation (send): " ++
           show (view cur lab) ++
           " ⊑ " ++ show name)
  d <- label me a
  Net.send s (encode d)

recv :: forall m a . (MonadIO m, MonadMask m, MonadFLAMIO m) => LSocket a -> m (Maybe (Labeled Principal a))
recv (LSocket (s, name)) = do
  Net.recv s (maxSize (undefined :: Labeled Principal a)) >>= \case
    Nothing -> return Nothing
    Just x -> do
      case decode x of
        Nothing -> return Nothing
        Just y -> return $ Just y

recvDelegate :: (MonadIO m, MonadMask m, MonadFLAMIO m) => LSocket a -> m Bool
recvDelegate (LSocket (s, name)) = do
  Net.recv s (maxSize (undefined :: Labeled Principal (Principal, Principal))) >>= \case
    Nothing -> return False
    Just x -> do
      case decode x of
        Nothing -> return False
        Just lab -> do
          h <- liftLIO getState
          liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
          liftLIO $ setState (H $ Set.insert lab (unH h))
          return True

sendDelegate :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel b Principal, ToLabel c Principal, ToLabel d Principal) =>
                LSocket a -> b -> c -> d -> m ()
sendDelegate (LSocket (s, name)) p q r = do
  lbl <- getLabel
  (,) <$> lbl ≽ (∇) q <*> (∇) (p →) ≽ (∇) (q →) >>= \case
    (True, True) -> do
      lab <- label r (normalize (p %), normalize (q %))
      bounds <- liftLIO $ gets $ view _1
      b <- view cur bounds ⊑ name
      unless b $
        fail ("IFC violation (sendDelegate): " ++
              show (view cur bounds) ++
              " ⊑ " ++ show name)
      Net.send s (encode lab)
    (False, _) -> error $ "IFC violation (sendDelegate 1): " ++ show lbl ++ " ≽ " ++ show ((∇) q)
    (_, False) -> error $ "IFC violation (sendDelegate 2): " ++ show ((∇) (p →)) ++ " ≽ " ++ show ((∇) (q →))
