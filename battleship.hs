{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE ScopedTypeVariables, GeneralizedNewtypeDeriving, LambdaCase, TemplateHaskell #-}

module Battleship where
import Lib.FLAM
import Lib.LIO
import qualified Data.List as List
import qualified Data.ByteString as B
import Control.Monad.State
import Control.Arrow
import Control.Lens
import Control.Lens.Traversal

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

data BattleshipData = BattleShipData { _ships :: Labeled FLAM [Ship], _hits :: [Hit] }

makeLenses ''BattleshipData

type BattleshipT = StateT BattleshipData

evalBattleshipT :: Monad m => BattleshipT m a -> Labeled FLAM [Ship] -> m a 
evalBattleshipT m ships = evalStateT m (BattleShipData ships [])

getShips :: Monad m => BattleshipT m (Labeled FLAM [Ship])
getShips = gets (view ships)

getHits :: Monad m => BattleshipT m [Hit]
getHits = gets (view hits)

addHit :: Monad m => Hit -> BattleshipT m ()
addHit = modify . over hits . (:)

modifyM :: (Monad m) => (s -> m s) -> StateT s m ()
modifyM f = get >>= (lift . f) >>= put

clear :: (MonadLIO H Principal m, MonadFLAMIO m) => Coordinate -> BattleshipT m ()
clear c = modifyM $ mapMOf ships $ \lab -> do
            ships <- unlabel lab
            clr <- getClearance
            label clr (List.map (List.delete c) ships)

dead :: (MonadLIO H Principal m, MonadFLAMIO m) => BattleshipT m Bool
dead = List.all List.null <$> (getShips >>= unlabel)

alive :: (MonadLIO H Principal m, MonadFLAMIO m) => BattleshipT m Bool
alive = not <$> dead

onCoordinate :: Coordinate -> Ship -> Bool
onCoordinate _ [] = False
onCoordinate c (c':s)
  | c == c' = True
  | otherwise = onCoordinate c s

hasShip :: (MonadLIO H Principal m, MonadFLAMIO m) => Coordinate -> BattleshipT m Bool
hasShip (x, y) = List.any (onCoordinate (x, y)) <$> (getShips >>= unlabel)

isHit :: Monad m => Coordinate -> BattleshipT m Bool
isHit c = List.any ((== c) . fst) <$> getHits

renderOwn :: (MonadLIO H Principal m, MonadFLAMIO m) => BattleshipT m String
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
  clr <- getClearance
  send socket clr $ Attack (r x, c y)
  done <-
    lift (recv socket) >>= \case
      Just lb -> unlabel lb >>= \case
        Hit -> do
          liftIO $ putStrLn "Hit!"
          addHit ((r x, c y), True)
          return False
        Miss -> do
          liftIO $ putStrLn "Miss!"
          addHit ((r x, c y), False)
          return False
        YouSankMyBattleship -> do
          liftIO $ putStrLn "You sank my battleship!"
          addHit ((r x, c y), True)
          return True
        msg -> error $ "Unexpected message: " ++ show msg
      Nothing -> error "Error receiving message!"
  renderTheirs >>= liftIO . putStrLn
  unless done $ await socket

await :: LSocket Msg -> BattleshipT FLAMIO ()
await socket = do
  clr <- getClearance
  done <-
    lift (recv socket) >>= \case
      Just lb -> do
        unlabel lb >>= \case
          Attack (x, y) -> do
            liftIO $ putStrLn $ (show x ++ ", " ++ show y) ++ " was attacked!"
            z <- "Client" ⊑ "Server"
            liftLIO $ liftIO $ print z
            hasShip (x, y) >>= \case
              True -> do
                clear (x, y)
                alive >>= \case
                  True -> do send socket clr Hit
                             return False
                  False -> do send socket clr YouSankMyBattleship
                              return True
              False -> do send socket clr Miss
                          return False
          msg -> error $ "Unexpected message: " ++ show msg
      Nothing -> error "Error receiving message!"
  renderOwn >>= liftIO . putStrLn
  unless done $ attack socket
