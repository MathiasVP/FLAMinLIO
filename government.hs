{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PostfixOperators #-}

module Government where

import Lib.FLAM
import Lib.LIO
import Lib.Network
import Lib.RPC
import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Lens

asUser :: (ToLabel a Principal, MonadFLAMIO m) => a -> m () -> m ()
asUser u m = do
  label <- getLabel
  clr <- getClearance
  liftFLAMIO $ FLAMIO $ AssumptionsT $ lift $ modify (cache .~ emptyCache)
  liftLIO $ modify $ _1 . cur .~ ((⊥) →) ∧ (u ←)
  liftLIO $ modify $ _1 . clearance .~ (u →) ∧ ((⊥) ←)
  _ <- m
  liftLIO $ modify $ _1 . clearance .~ clr
  liftLIO $ modify $ _1 . cur .~ label

example :: FLAMIO ()
example = do
  asUser "CIA" $ do
    addDelegate ("CIA" .: "B") "CIA" "CIA"
    addDelegate ("CIA" .: "A") "CIA" "CIA"

  asUser ("CIA" .: "A") $ do
    clr <- getClearance
    withStrategy ["CIA"] $ do
      -- A is an agent. He/She can verify the identity of agent B
      liftIO $ putStrLn $ "I am agent " ++ show clr ++ "! Are you an agent as well?"
      x <- ("CIA" .: "B") ≽ "CIA"
      liftIO $ print x

  asUser ("CIA" .: "B") $ do
    clr <- getClearance
    withStrategy ["CIA"] $ do
      -- B is an agent. He/She can verify the identity of A
      liftIO $ putStrLn $ "I am agent " ++ show clr ++ "! Are you an agent as well?"
      x <- ("CIA" .: "A") ≽ "CIA"
      liftIO $ print x

  asUser ("CIA" .: "C") $ do
    clr <- getClearance
    withStrategy ["CIA"] $ do
      -- Note: C is not an agent. He/She cannot know that A is an agent
      liftIO $ putStrLn $ "I am agent " ++ show clr ++ "! Are you an agent as well?"
      x <- ("CIA" .: "A") ≽ "CIA"
      liftIO $ print x

  asUser ("CIA" .: "B") $ do
    clr <- getClearance
    withStrategy ["CIA"] $ do
      -- B is an agent. He/She can verify the identity of B and know that C is not an agent
      liftIO $ putStrLn $ "I am agent " ++ show clr ++ "! Are you an agent as well?"
      x <- ("CIA" .: "C") ≽ "CIA" -- Identity cannot be verified by CIA
      liftIO $ print x

main :: IO ()
main = runFLAM "CIA" example
