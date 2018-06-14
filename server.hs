{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables, LambdaCase, PostfixOperators #-}

module Example.Network where
import Lib.FLAM hiding ((≽))
import Lib.LIO
import Control.Monad.State
import Control.Lens
import Battleship hiding (ships)
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

ships :: FLAMIO (Labeled Principal [Ship])
ships = label ("Server" %) [ship1, ship2, ship3, ship4, ship5, ship6, ship7, ship8]

(≽) :: (ToLabel a Principal, ToLabel b Principal) => a -> b -> (a, b)
p ≽ q = (p, q)

{- This is an example of an unfortunate circularity where we need to prove l1 actsfor l2 and
   l2 = clr and l1 = ldel join cur, where ldel is a label on a delegation we need to use.
   How can we resolve this? -}
example :: FLAMIO ()
example = do
  addDelegate (("Server" →) ≽ ("Client" →)) bot
  addDelegate (("Client" ←) ≽ ("Server" ←)) bot
  liftLIO $ modify $ (_1 . cur) .~ ("Client" %)
  withStrategy [bot] $ do
    x <- "Client" ⊑ "Server"
    liftIO $ print x
    {-serve ("127.0.0.1", "8000", "Client") $ \(socket :: LSocket Msg) -> do
      ships >>= evalBattleshipT (await socket)-}
  return ()

runExample :: IO ()
runExample =
  evalStateT (unLIO (runFLAM example))
  (BoundedLabel { _cur = bot, _clearance = ("Server" %) }, H Set.empty, [])
