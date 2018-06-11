{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
{-# OPTIONS_GHC -v #-}

module Example.Network where
import Lib.FLAM
import Lib.LIO
import Control.Monad.State
import Battleship
import qualified Data.Set as Set

ship1, ship2, ship3, ship4, ship5, ship6, ship7, ship8 :: Ship
ship1 = [(r 0, c 0), (r 0, c 1)]
ship2 = [(r 0, c 3), (r 1, c 3), (r 2, c 3)]
ship3 = [(r 0, c 6), (r 0, c 7), (r 0, c 8), (r 0, c 9)]
ship4 = [(r 3, c 0), (r 4, c 0), (r 5, c 0), (r 6, c 0)]
ship5 = [(r 5, c 5), (r 6, c 5)]
ship6 = [(r 5, c 9), (r 6, c 9), (r 7, c 9)]
ship7 = [(r 8, c 0), (r 8, c 1)]
ship8 = [(r 9, c 4), (r 9, c 5), (r 9, c 6), (r 9, c 7), (r 9, c 8), (r 9, c 9)]

ships :: [Ship]
ships = [ship1, ship2, ship3, ship4, ship5, ship6, ship7, ship8]

example :: FLAMIO ()
example = do
  serve ("127.0.0.1", "8000", "Client") $ \(socket :: LSocket Msg) -> do
    recv socket >>= \case
      
    evalBattleshipT (await socket) ships
  return ()

runExample :: IO ()
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = top }, H Set.empty, [])
