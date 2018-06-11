{-# LANGUAGE ScopedTypeVariables, GeneralizedNewtypeDeriving, LambdaCase #-}

module Battleship where
import FLAM
import LIO
import TCB
import qualified Data.List as List
import qualified Data.ByteString as B
import Control.Monad.State
import Control.Arrow

type Line = [Bool]
type Grid = [Line]

newtype Row = Row Int
  deriving (Num, Eq, Ord, Enum, Show)

newtype Column = Column Int
  deriving (Num, Eq, Ord, Enum, Show)

type Coordinate = (Row, Column)
type Ship = [Coordinate]

type Hit = (Coordinate, Bool)

r :: Int -> Row
r = Row

c :: Int -> Column
c = Column

type BattleshipT = StateT ([Ship], [Hit])

evalBattleshipT :: Monad m => BattleshipT m a -> [Ship] -> m a 
evalBattleshipT m ships = evalStateT m (ships, [])

getShips :: Monad m => BattleshipT m [Ship]
getShips = gets fst

getHits :: Monad m => BattleshipT m [Hit]
getHits = gets snd

addHit :: Monad m => Hit -> BattleshipT m ()
addHit = modify . second . (:)

clear :: Monad m => Coordinate -> BattleshipT m ()
clear c = modify $ first $ List.map (List.delete c)

dead :: Monad m => BattleshipT m Bool
dead = List.all List.null <$> getShips

alive :: Monad m => BattleshipT m Bool
alive = not <$> dead

onCoordinate :: Coordinate -> Ship -> Bool
onCoordinate _ [] = False
onCoordinate c (c':s)
  | c == c' = True
  | otherwise = onCoordinate c s

hasShip :: Monad m => Coordinate -> BattleshipT m Bool
hasShip (x, y) = List.any (onCoordinate (x, y)) <$> getShips

isHit :: Monad m => Coordinate -> BattleshipT m Bool
isHit c = List.any ((== c) . fst) <$> getHits

renderOwn :: Monad m => BattleshipT m String
renderOwn = unlines <$> mapM renderLine [0..9]
  where renderLine x = mapM renderColumn [0..9]
          where renderColumn y =
                  hasShip (x, y) >>= \case
                    True -> return 'O'
                    False -> return ' '

renderTheirs :: Monad m => BattleshipT m String
renderTheirs = unlines <$> mapM renderLine [0..9]
  where renderLine x = mapM renderColumn [0..9]
          where renderColumn y =
                  isHit (x, y) >>= \case
                    True -> return 'X'
                    False -> return ' '

data Msg
  = Attack Coordinate
  | Hit
  | Miss
  | YouSankMyBattleship
  deriving Show

instance Serializable Row where
  encode (Row n) = encode n
  decode x = Row <$> decode x
  maxSize _ = maxSize (undefined :: Int)

instance Serializable Column where
  encode (Column n) = encode n
  decode x = Column <$> decode x
  maxSize _ = maxSize (undefined :: Int)

instance Serializable Msg where
  encode (Attack c) = B.cons 0 (encode c)
  encode Hit = B.singleton 1
  encode Miss = B.singleton 2
  encode YouSankMyBattleship = B.singleton 3

  decode bs = 
    case B.uncons bs of
      Just (0, bs') -> Attack <$> decode bs'
      Just (1, _) -> Just Hit
      Just (2, _) -> Just Miss
      Just (3, _) -> Just YouSankMyBattleship

  maxSize _ = 1 + maxSize (undefined :: Coordinate)

attack :: LSocket Msg -> BattleshipT FLAMIO ()
attack socket = do
  renderTheirs >>= liftIO . putStrLn
  liftIO $ putStr "> x = "
  x <- liftIO (read <$> getLine)
  liftIO $ putStr "> y = "
  y <- liftIO (read <$> getLine)
  send socket $ Attack (r x, c y)
  done <-
    lift (recv socket) >>= unlabel >>= \case
      Just Hit -> do
        liftIO $ putStrLn "Hit!"
        addHit ((r x, c y), True)
        return False
      Just Miss -> do
        liftIO $ putStrLn "Miss!"
        addHit ((r x, c y), False)
        return False
      Just YouSankMyBattleship -> do
        liftIO $ putStrLn "You sank my battleship!"
        addHit ((r x, c y), True)
        return True
      Just msg -> error $ "Unexpected message: " ++ show msg
  renderTheirs >>= liftIO . putStrLn
  unless done $ await socket

await :: LSocket Msg -> BattleshipT FLAMIO ()
await socket = do
  done <-
    lift (recv socket) >>= unlabel >>= \case
      Just (Attack (x, y)) -> do
        liftIO $ putStrLn $ (show x ++ ", " ++ show y) ++ " was attacked!"
        hasShip (x, y) >>= \case
          True -> do
            clear (x, y)
            alive >>= \case
              True -> do send socket Hit
                         return False
              False -> do send socket YouSankMyBattleship
                          return True
          False -> do send socket Miss
                      return False
      Just msg -> error $ "Unexpected message: " ++ show msg
  renderOwn >>= liftIO . putStrLn
  unless done $ attack socket
