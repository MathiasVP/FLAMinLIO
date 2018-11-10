{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
module Lib.FLAM where

import Prelude hiding ((^))
import Lib.LIO
import Lib.SendRecv
import Lib.TCB()
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Map.Strict(Map)
import qualified Data.Set as Set
import Data.Set(Set, (\\))
import Data.Either
import Control.Monad.State
import Control.Arrow
import Control.Lens.Tuple
import Control.Lens hiding ((:<))
import Control.Monad.Extra
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Maybe
import qualified Data.POMap.Strict as POMap
import Data.POMap.Strict(POMap)
import Algebra.PartialOrd
import Algebra.Lattice.Op
import Data.Foldable
import Data.Typeable
import Data.Dynamic.Binary
import GHC.Generics
import qualified Data.ByteString.Lazy as BL
import qualified Data.Binary as Bin
import Data.Binary(Binary, Get, Put)
import Control.Concurrent.Forkable
import GHC.Read
import qualified Text.ParserCombinators.ReadPrec as R
import Text.ParserCombinators.ReadPrec((<++))
import Control.Exception hiding (mask, try)
import Control.Monad.Catch
import Control.Concurrent.Chan

import qualified Network.Simple.TCP as Net
import qualified Network.Socket as NS

listview :: Ord a => Set a -> [a]
listview = Set.toList

setview :: Ord a => Set a -> Maybe (a, Set a)
setview = Set.minView

mapview :: Map k a -> Maybe ((k, a), Map k a)
mapview = Map.minViewWithKey

data Principal
  = (:⊤)
  | (:⊥)
  | Name !String
  | !Principal :/\ !Principal
  | !Principal :\/ !Principal
  | (:→) !Principal
  | (:←) !Principal
  | !Principal ::: !Principal
  deriving (Eq, Ord, Generic, Read)

instance Binary Principal

instance Show Principal where
  showsPrec _ (:⊤) = showString "⊤"
  showsPrec _ (:⊥) = showString "⊥"
  showsPrec _ (Name s) = showString s
  showsPrec n (p :/\ q) =
    if n > 10 then showString "(" . showsPrec 11 p . showString " ∧ " . showsPrec 11 q . showString ")"
    else showsPrec 11 p . showString " ∧ " . showsPrec 11 q
  showsPrec n (p :\/ q) =
    if n > 10 then showString "(" . showsPrec 11 p . showString " ∨ " . showsPrec 11 q . showString ")"
    else showsPrec 11 p . showString " ∨ " . showsPrec 11 q
  showsPrec n ((:→) p) =
    if n > 10 then showString "(" . showsPrec 11 p . showString " →" . showString ")"
    else showsPrec 11 p . showString " →"
  showsPrec n ((:←) p) =
    if n > 10 then showString "(" . showsPrec 11 p . showString " ←" . showString ")"
    else showsPrec 11 p . showString " ←"
  showsPrec n (p ::: q) =
    if n > 10 then showString "(" . showsPrec 11 p . showString " : " . showsPrec 11 q . showString ")"
    else showsPrec 11 p . showString " : " . showsPrec 11 q
  
newtype H = H { unH :: Set (Labeled Principal (Principal, Principal)) }
  deriving (Ord, Eq, Show, Generic, Binary)

data L
  = N !String
  | T
  | B
  | !L :.: !L
  deriving (Eq, Ord, Generic)

instance Binary L

instance Show L where
  show (N s) = s
  show T = "⊤"
  show B = "⊥"
  show (l1 :.: l2) = show l1 ++ " : " ++ show l2

newtype M = M { unM :: Set L } -- L₁ \/ L₂ \/ ... \/ Lₙ
  deriving (Eq, Ord, Generic, Binary)

instance Show M where
  show (M ls) = show' (Set.toList ls)
    where show' [] = ""
          show' [l] = show l
          show' (l : ls') = show l ++ " ∨ " ++ show' ls'

newtype J = J { unJ :: Set M } -- M₁ /\ M₂ /\ ... /\ Mₙ
  deriving (Eq, Ord, Generic, Binary)

instance Show J where
  show (J ms) = show' (Set.toList ms)
    where show' [] = ""
          show' [m] = show m
          show' (m : ms') = show m ++ " ∧ " ++ show' ms'

data JNF = JNF { confidentiality :: !J, integrity :: !J }
  deriving (Eq, Ord)

instance Show JNF where
  show (JNF c i) = "(" ++ show c ++ ") → ∧ (" ++ show i ++ ") ←"

data ProgressCondition
  = ActsFor !Principal !Principal
  | Conj !(ProgressCondition) !(ProgressCondition)
  | Disj !(ProgressCondition) !(ProgressCondition)
  | TrueCondition
  | FalseCondition
  deriving (Eq, Generic)

instance Binary ProgressCondition

instance Show (ProgressCondition) where
  showsPrec n (ActsFor x y) =
    if n > 10 then showString "(" . showsPrec 11 x . showString " ≽ " . showsPrec 11 y . showString ")"
    else showsPrec 11 x . showString " ≽ " . showsPrec 11 y
  showsPrec n (Conj pc1 pc2) =
    if n > 10 then showString "(" . showsPrec 11 pc1 . showString " ∧ " . showsPrec 11 pc2 . showString ")"
    else showsPrec 11 pc1 . showString " ∧ " . showsPrec 11 pc2
  showsPrec n (Disj pc1 pc2) =
    if n > 10 then showString "(" . showsPrec 11 pc1 . showString " ∨ " . showsPrec 11 pc2 . showString ")"
    else showsPrec 11 pc1 . showString " ∨ " . showsPrec 11 pc2
  showsPrec _ TrueCondition = showString "True"
  showsPrec _ FalseCondition = showString "False"

type ForwardCache = Map Principal (Map (Principal, Principal) Bool)
type Assumptions = Set (Principal, Principal)
newtype AssumptionsT m a = AssumptionsT { unAssumptionsT :: StateT ForwardCache (ReaderT (Assumptions, Set Principal) m) a }
  deriving (Functor, Applicative, Monad, MonadState ForwardCache, MonadReader (Assumptions, Set Principal), MonadIO)

instance (PartialOrd a, PartialOrd b, PartialOrd c) => PartialOrd (a, b, c) where
  (a1, b1, c1) `leq` (a2, b2, c2) = a1 `leq` a2 && b1 `leq` b2 && c1 `leq` c2

instance (PartialOrd a, PartialOrd b, PartialOrd c, PartialOrd d) => PartialOrd (a, b, c, d) where
  (a1, b1, c1, d1) `leq` (a2, b2, c2, d2) = a1 `leq` a2 && b1 `leq` b2 && c1 `leq` c2 && d1 `leq` d2

instance PartialOrd Principal where
  x `leq` y = x <= y

instance PartialOrd H where
  H x `leq` H y = x `leq` y

type IP = String
type Port = String

data LSocket = LSocket { sendChan :: Chan BL.ByteString
                       , recvRPCCallChan :: Chan BL.ByteString
                       , recvRPCRetChan :: Chan BL.ByteString
                       , recvFwdQueryChan :: Chan BL.ByteString
                       , recvFwdResChan :: Chan BL.ByteString
                       , channelLabel :: Principal }
  deriving (Eq, Generic)

type SureCache = Map (Principal, Principal) (Map (Principal, Principal) Principal)
type UnsureCache = Map (Principal, Principal) (ProgressCondition)

type ReachabilityCache = Map (Set ((Principal, Principal), Assumptions)) ((Set ((J, J), Assumptions), Set ((J, J), Assumptions)))
type ProvedCache = POMap (Assumptions, Strategy Principal, H, [LSocket]) SureCache
type PrunedCache = Map Assumptions (Map (Principal, Principal) UnsureCache)
type FailedCache = POMap (Op (Assumptions, Strategy Principal, H, [LSocket])) SureCache
data Cache = Cache { _reachabilityCache :: !ReachabilityCache,
                     _provedCache :: !ProvedCache,
                     _prunedCache :: !PrunedCache,
                     _failedCache :: !FailedCache }

makeLenses ''Cache

emptyCache :: Cache
emptyCache = Cache { _reachabilityCache = Map.empty,
                     _provedCache = POMap.empty,
                     _prunedCache = Map.empty,
                     _failedCache = POMap.empty }

newtype Original t = Original t
newtype Replacement t = Replacement t
newtype Pattern t = Pattern t

-- substitute oldpc newpc pc means pc[oldpc -> newpc]
substitute :: Pattern ProgressCondition -> Replacement ProgressCondition -> Original ProgressCondition -> ProgressCondition
substitute (Pattern oldpc) (Replacement newpc) (Original pc) | oldpc == pc = newpc
substitute oldpc newpc (Original (Conj pc1 pc2)) =
  Conj (substitute oldpc newpc (Original pc1)) (substitute oldpc newpc (Original pc2))
substitute oldpc newpc (Original (Disj pc1 pc2)) =
  Disj (substitute oldpc newpc (Original pc1)) (substitute oldpc newpc (Original pc2))
substitute _ _ (Original pc) = pc

data QueryResult
  = Failed !Assumptions
  | Success !Assumptions
  | Pruned !(ProgressCondition) !Assumptions
  deriving Show

(^) :: QueryResult -> Assumptions -> QueryResult
Failed a ^ _ = Failed a
Success a1 ^ a2 = Success (Set.union a1 a2)
Pruned pc a1 ^ a2 = Pruned pc (Set.union a1 a2)

(^!) :: QueryResult -> Assumptions -> QueryResult
Failed a1 ^! a2 = Failed (Set.union a1 a2)
Success a ^! _ = Success a
Pruned pc a1 ^! a2 = Pruned pc (Set.union a1 a2)

liftB :: Assumptions -> Bool -> QueryResult
liftB a True = Success a
liftB a False = Failed a

class (MonadLIO Principal m) => MonadFLAMIO m where
  liftFLAMIO :: FLAMIO a -> m a

instance (MonadLIO l m, Monoid a) => MonadLIO l (WriterT a m) where 
  liftLIO m = WriterT $ liftLIO m >>= \a -> return (a, mempty)
  
instance (MonadFLAMIO m, Monoid a) => MonadFLAMIO (WriterT a m) where
  liftFLAMIO m = WriterT $ liftFLAMIO m >>= \a -> return (a, mempty)

newtype FLAMIO a = FLAMIO { unFLAMIO :: AssumptionsT (StateT FLAMIOSt (LIO FLAM)) a }
  deriving (Functor, Applicative, Monad)

lowerB' :: MonadFLAMIO m => QueryResult -> m (Bool, Assumptions)
lowerB' (Success a) = return (True, a)
lowerB' (Failed a) = return (False, a)
lowerB' (Pruned pc a) =
  isTrue a pc >>= \case
    Just b -> return (b, a)
    Nothing -> return (False, a)

lowerB :: MonadFLAMIO m => QueryResult -> m Bool
lowerB r = fst <$> lowerB'  r

setFilterMapM :: (Ord a, Ord b, Monad m) => (a -> m (Maybe b)) -> Set a -> m (Set b)
setFilterMapM f s = visit s Set.empty
  where visit (setview -> Nothing) s = return s
        visit (setview -> Just (a, as)) s =
          f a >>= \case
            Nothing -> visit as s
            Just b -> visit as (Set.insert b s)

(<&&&>) :: (Monad m) => m QueryResult -> m QueryResult -> m QueryResult
(<&&&>) m1 m2 =
  m1 >>= \case
    Success a -> (^) <$> m2 <*> pure a
    Failed a -> return $ Failed a
    Pruned pc1 a1 ->
      m2 >>= \case
        Success a2 -> return $ Pruned pc1 (a1 `Set.union` a2)
        Failed a2 -> return $ Failed (a1 `Set.union` a2)
        Pruned pc2 a2 -> return $ Pruned (pc1 `Conj` pc2) (a1 `Set.union` a2)
infixr 8 <&&&>

(<|||>) :: (Monad m) => m QueryResult -> m QueryResult -> m QueryResult
(<|||>) m1 m2 =
  m1 >>= \case
    Success a -> return $ Success a
    Failed a -> (^!) <$> m2 <*> pure a
    Pruned pc1 a1 ->
      m2 >>= \case
        Success a2 -> return $ Success (a1 `Set.union` a2)
        Failed a2 -> return $ Pruned pc1 (a1 `Set.union` a2)
        Pruned pc2 a2 -> return $ Pruned (pc1 `Disj` pc2) (a1 `Set.union` a2)
infixr 7 <|||>

mapMapMaybeM :: (Monad m, Ord k) => (a -> m (Maybe b)) -> Map k a -> m (Map k b)
mapMapMaybeM f m = do
  let xs = Map.toList m
  ys <- mapMaybeM (f . snd) xs
  return $ Map.fromList (zipWith (\(k, _) y -> (k, y)) xs ys)

mapMapWithKeyM :: (Monad m, Ord k) => (k -> a -> m b) -> Map k a -> m (Map k b)
mapMapWithKeyM f m = do
  let xs = Map.toList m
  ys <- mapM (uncurry f) xs
  return $ Map.fromList (zipWith (\(k, _) y -> (k, y)) xs ys)

isTrue :: MonadFLAMIO m => Assumptions -> ProgressCondition -> m (Maybe Bool)
isTrue a (ActsFor p q) = do
  (b, _) <- reach (p, q) (Set.map (, Set.empty) a)
  case b of
    True -> return $ Just True
    False -> return Nothing
isTrue a (Conj pc1 pc2) =
  isTrue a pc1 >>= \case
    Just True -> isTrue a pc2
    Just False -> return $ Just False
    Nothing -> return $ Nothing
isTrue a (Disj pc1 pc2) =
 isTrue a pc1 >>= \case
   Just True -> return $ Just True
   Just False -> isTrue a pc1
   Nothing -> return $ Nothing
isTrue _ TrueCondition = return $ Just True
isTrue _ FalseCondition = return $ Just False

isFalse :: MonadFLAMIO m => Assumptions -> ProgressCondition -> m (Maybe Bool)
isFalse a pc =
  isTrue a pc >>= \case
    Just b -> return $ Just $ not b
    Nothing -> return $ Nothing

mapMaybeKeepM :: (Ord k, Monad m) => (a -> m (Maybe b)) -> Map k a -> m (Map k a, Map k b)
mapMaybeKeepM _ (mapview -> Nothing) = return (Map.empty, Map.empty)
mapMaybeKeepM f (mapview -> Just ((k, a), m)) = do
  (m1, m2) <- mapMaybeKeepM f m
  f a >>= \case
    Just b -> return (m1, Map.insert k b m2)
    Nothing -> return (Map.insert k a m1, m2)

alterSure :: (Maybe (Map (Principal, Principal) Principal) ->
              Maybe (Map (Principal, Principal) Principal)) ->
             Principal -> Principal ->
             Maybe SureCache -> Maybe SureCache
alterSure f cur clr Nothing = Map.singleton (cur, clr) <$> f Nothing
alterSure f cur clr (Just m) = Map.insert (cur, clr) <$> f (Map.lookup (cur, clr) m) <*> pure m

insert p q cur Nothing = Map.singleton (p, q) cur
insert p q cur (Just map) = Map.insert (p, q) cur map

updatePruned :: (Monad m) => Principal -> Principal -> ProgressCondition ->
                (ProgressCondition -> m (Maybe Bool)) -> ProgressCondition ->
                m (Maybe ProgressCondition)
updatePruned p q rep cond pc =
 let pc' = substitute (Pattern (ActsFor p q)) (Replacement rep) (Original pc)
 in cond pc' >>= \case
      Just True -> return Nothing
      Just False -> return $ Just pc'
      Nothing -> return $ Just pc'

adjustPOMapGT :: PartialOrd k => (a -> a) -> k -> POMap k a -> POMap k a
adjustPOMapGT f k m =
  let m' = POMap.dropWhileAntitone (`leq` k) m
  in POMap.foldlWithKey' insert m m'
  where insert m k a = POMap.insert k (f a) m

adjustMapGE :: Ord k => (a -> a) -> k -> Map k a -> Map k a
adjustMapGE f k m =
  let m' = Map.dropWhileAntitone (<= k) m
  in case Map.lookup k m of
       Nothing -> Map.foldlWithKey' insert m m'
       Just v -> Map.insert k (f v) $ Map.foldlWithKey' insert m m'
     where insert m k v = Map.insert k (f v) m

adjustMapLE :: Ord k => (a -> a) -> k -> Map k a -> Map k a
adjustMapLE f k m =
  let m' = Map.takeWhileAntitone (<= k) m
  in case Map.lookup k m of
       Nothing -> Map.foldlWithKey' insert m m'
       Just v -> Map.insert k (f v) $ Map.foldlWithKey' insert m m'
     where insert m k v = Map.insert k (f v) m

adjustOrInsert :: Ord k => (Maybe a -> a) -> k -> Map k a -> Map k a
adjustOrInsert f k m =
  case Map.lookup k m of
    Just v -> Map.insert k (f (Just v)) m
    Nothing -> Map.insert k (f Nothing) m

modifyCache :: MonadFLAMIO m => (Cache -> Cache) -> m ()
modifyCache f = liftFLAMIO $ FLAMIO $ lift $ modify $ over cache f

getsCache :: MonadFLAMIO m => (Cache -> a) -> m a
getsCache f = liftFLAMIO $ FLAMIO $ lift $ gets $ views cache f

getCache :: MonadFLAMIO m =>  m Cache
getCache = liftFLAMIO $ FLAMIO $ lift $ gets $ view cache

update :: forall m . MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> QueryResult -> m ()
update (cur, clr) (p, q) (Success a) = do
  cur' <- liftLIO getLabel
  h <- getH
  strat <- liftLIO $ gets $ view _2
  useSockets $ \socks -> do
    liftFLAMIO $ modifyCache $ over provedCache $ adjustPOMapGT (adjustOrInsert (insert p q cur') (cur, clr)) (a, strat, h, socks)
    liftFLAMIO $ modifyCache $ over provedCache $ POMap.alter (alterSure (Just . insert p q cur') cur clr) (a, strat, h, socks)
    liftFLAMIO $ modifyCache $ over prunedCache $ adjustMapGE (Map.adjust (Map.delete (p, q)) (cur, clr)) a
  prunedmap <- Map.lookup a <$> liftFLAMIO (getsCache (view prunedCache)) >>= \case
    Just prunedmap ->
      case Map.lookup (cur, clr) prunedmap of
        Just pm -> mapMapMaybeM (updatePruned p q TrueCondition (isTrue a)) pm
        Nothing -> return Map.empty
    Nothing -> return Map.empty
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.alter (Just . insert cur clr prunedmap) a
  
update (cur, clr) (p, q) (Pruned pc a) = do
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _2
  liftFLAMIO $ modifyCache $ over prunedCache $ adjustOrInsert
    (\case
        Just m -> Map.alter (Just . insert p q pc) (cur, clr) m
        Nothing -> Map.singleton (cur, clr) (Map.singleton (p, q) pc)) a
  prunedmap <- Map.lookup a <$> liftFLAMIO (getsCache (view prunedCache)) >>= \case
    Just prunedmap ->
      case Map.lookup (cur, clr) prunedmap of
        Just pm -> return $ Map.map updatePruned pm
        Nothing -> return Map.empty
    Nothing -> return Map.empty
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.alter (Just . insert cur clr prunedmap) a
  where updatePruned :: ProgressCondition -> ProgressCondition
        updatePruned = substitute (Pattern (ActsFor p q)) (Replacement pc) . Original

update (cur, clr) (p, q) (Failed a) = do
  cur' <- liftLIO getLabel
  h <- getH
  strat <- liftLIO $ gets $ view _2
  useSockets $ \socks -> do
    liftFLAMIO $ modifyCache $ over failedCache $ adjustPOMapGT (adjustOrInsert (insert p q cur') (cur, clr)) (Op (a, strat, h, socks))
    liftFLAMIO $ modifyCache $ over failedCache $ POMap.alter (alterSure (Just . insert p q cur') cur clr) (Op (a, strat, h, socks))
    liftFLAMIO $ modifyCache $ over prunedCache $ adjustMapLE (Map.adjust (Map.delete (p, q)) (cur, clr)) a
  pruned <- Map.takeWhileAntitone (`leq` a) <$> (liftFLAMIO $ getsCache $ view prunedCache)
  forM_ (Map.toList pruned) $ \(assumptions, prunedmap) ->
    case Map.lookup (cur, clr) prunedmap of
      Just m -> do
        (new', pruned') <- mapMaybeKeepM (updatePruned p q FalseCondition (isFalse assumptions)) m
        let adjust :: Maybe UnsureCache -> UnsureCache
            adjust Nothing = pruned'
            adjust (Just m) = Map.union pruned' m
        mapM_ (\(p, q) -> update (cur, clr) (p, q) (Failed assumptions)) (Map.keys new')
      Nothing -> return ()

searchSurePOMap :: (Principal, Principal) -> (Principal, Principal) ->
                   POMap (Assumptions, Strategy Principal, H, [LSocket]) SureCache -> Maybe (Principal, Assumptions)
searchSurePOMap (cur, clr) (p, q) m = search (POMap.toList m)
  where search [] = Nothing
        search (((a, _, _, _), c) : cs) =
          case Map.lookup (cur, clr) c of
          Just m -> case Map.lookup (p, q) m of
                      Just p -> Just (p, a)
                      Nothing -> search cs
          Nothing -> search cs

searchSurePOMapOp :: (Principal, Principal) -> (Principal, Principal) ->
                     POMap (Op (Assumptions, Strategy Principal, H, [LSocket])) SureCache -> Maybe (Principal, Assumptions)
searchSurePOMapOp (cur, clr) (p, q) m = search (POMap.toList m)
  where search [] = Nothing
        search ((Op (a, _, _, _), c) : cs) =
          case Map.lookup (cur, clr) c of
          Just m -> case Map.lookup (p, q) m of
                      Just p -> Just (p, a)
                      Nothing -> search cs
          Nothing -> search cs

getAssumptions :: MonadFLAMIO m => m Assumptions
getAssumptions = liftFLAMIO $ FLAMIO $ asks (view _1)

getForwardCache :: MonadFLAMIO m => m ForwardCache
getForwardCache = liftFLAMIO $ FLAMIO $ get

canForwardTo :: MonadFLAMIO m => Principal -> m Bool
canForwardTo s = do
  dontfwdto <- liftFLAMIO $ FLAMIO $ asks (view _2)
  return $ Set.notMember s dontfwdto

searchFailedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (Principal, Assumptions))
searchFailedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO getCache
  h <- getH
  strat <- liftLIO $ gets $ view _2
  assumptions <- getAssumptions
  useSockets $ \socks -> do
    let failedcache = POMap.takeWhileAntitone (`leq` Op (assumptions, strat, h, socks)) (view failedCache cache)
    return $ searchSurePOMapOp (cur, clr) (p, q) failedcache
  
searchProvedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (Principal, Assumptions))
searchProvedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO $ getCache
  h <- getH
  strat <- liftLIO $ gets $ view _2
  assumptions <- getAssumptions
  useSockets $ \socks -> do
    let provedcache = POMap.takeWhileAntitone (`leq` (assumptions, strat, h, socks)) (view provedCache cache)
    return $ searchSurePOMap (cur, clr) (p, q) provedcache
  
data CacheSearchResult
  = ProvedResult !Principal !Assumptions
  | FailedResult !Principal !Assumptions
  | PrunedResult !ProgressCondition !Assumptions

searchPrunedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (ProgressCondition, Assumptions))
searchPrunedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO getCache
  h <- getH
  strat <- liftLIO $ gets $ view _2
  assumptions <- getAssumptions
  case Map.lookup assumptions (view prunedCache cache) of
    Just uc ->
      case Map.lookup (cur, clr) uc of
        Just uc -> return ((,) <$> Map.lookup (p, q) uc <*> pure assumptions)
        Nothing -> return Nothing
    Nothing -> return Nothing

searchcache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe CacheSearchResult)
searchcache (cur, clr) (p, q) = do
  let failedSearch = searchFailedCache (cur, clr) (p, q)
      prunedSearch = searchPrunedCache (cur, clr) (p, q)
      provedSearch = searchProvedCache (cur, clr) (p, q)
  (,,) <$> provedSearch <*> failedSearch <*> prunedSearch >>= \case
    (Just (cur', a), _, _) -> return $ Just $ ProvedResult cur' a
    (_, Just (cur', a), _) -> return $ Just $ FailedResult cur' a
    (_, _, Just (pc, a)) -> return $ Just $ PrunedResult pc a
    (_, _, _) -> return Nothing

instance MonadLIO l m => MonadLIO l (AssumptionsT m) where
  liftLIO = lift . liftLIO
  
instance MonadTrans AssumptionsT where
  lift = AssumptionsT . lift . lift

incrD :: MonadFLAMIO m => m ()
incrD = liftFLAMIO $ FLAMIO $ lift $ modify $ over depth $ (+2) 

decrD :: MonadFLAMIO m => m ()
decrD = liftFLAMIO $ FLAMIO $ lift $ modify $ over depth $ (subtract 2)

getDepth :: MonadFLAMIO m => m Int
getDepth = liftFLAMIO $ FLAMIO $ lift $ gets (view depth)

(.≽.) :: MonadFLAMIO m => Principal -> Principal -> m QueryResult
p .≽. q = do
  assumptions <- getAssumptions
  curLab <- getLabel
  clrLab <- getClearance
  searchcache (curLab, clrLab) (p, q) >>= \case
    Just (ProvedResult cur' a) -> do
      liftLIO $ modify $ (_1 . cur) .~ cur'
      return $ Success a
    Just (FailedResult cur' a) -> do
      liftLIO $ modify $ (_1 . cur) .~ cur'
      return $ Failed a
    Just (PrunedResult pc a) -> do
      return $ Pruned pc a
    Nothing -> do
      d <- getDepth
      if d < 10 then do
        update (curLab, clrLab) (p, q) (Pruned (ActsFor p q) Set.empty)
        r <- (p .≽ q)
        update (curLab, clrLab) (p, q) r
        return r
      else return $ Failed Set.empty

bot_ :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
bot_ (_, (:⊥)) = return $ Success Set.empty
bot_ (_, (((:→) (:⊥)) :/\ ((:←) (:⊥)))) = return $ Success Set.empty
bot_ _ = return $ Failed Set.empty

top_ :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
top_ ((:⊤), _) = return $ Success Set.empty
top_ ((((:→) (:⊤)) :/\ ((:←) (:⊤))), _) = return $ Success Set.empty
top_ _ = return $ Failed Set.empty

refl :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
refl (p, q) | p == q = return $ Success Set.empty
refl _ = return $ Failed Set.empty

proj :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
proj ((:→) p, (:→) q) = p .≽. q
proj ((:←) p, (:←) q) = p .≽. q
proj _ = return $ Failed Set.empty

projR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
projR (p, (:←) q) | p == q = return $ Success Set.empty
projR (p, (:→) q) | p == q = return $ Success Set.empty
projR _ = return $ Failed Set.empty

own1 :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
own1 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. p'
own1 _ = return $ Failed Set.empty

own2 :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
own2 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. (o' ::: p')
own2 _ = return $ Failed Set.empty

conjL :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
conjL (p1 :/\ p2, p) = p1 .≽. p <|||> p2 .≽. p
conjL _ = return $ Failed Set.empty

conjR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
conjR (p, p1 :/\ p2) = p .≽. p1 <&&&> p .≽. p2
conjR _ = return $ Failed Set.empty

disjL :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
disjL (p1 :\/ p2, p) = p1 .≽. p <&&&> p2 .≽. p
disjL _ = return $ Failed Set.empty

disjR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
disjR (p, p1 :\/ p2) = p .≽. p1 <|||> p .≽. p2
disjR _ = return $ Failed Set.empty

reach :: MonadFLAMIO m => (Principal, Principal) -> Set ((Principal, Principal), Assumptions) -> m (Bool, Assumptions)
reach (p, q) s = do
  let pNorm = norm p
      qNorm = norm q

  (sconf, sint) <- 
    Map.lookup s <$> liftFLAMIO (getsCache $ view reachabilityCache) >>= \case
      Just (sconf, sint) -> return (sconf, sint)
      Nothing -> do
        let sconf, sint :: Set ((J, J), Assumptions)
            (sconf, sint) = (transitive *** transitive) .
                            (atomize *** atomize) . expand $ s
        liftFLAMIO $ modifyCache $ over reachabilityCache (Map.insert s (sconf, sint))
        return (sconf, sint)
  let sconf' = Map.fromList $ Set.elems sconf
      sint' = Map.fromList $ Set.elems sint
      f m (j1, j2) = case Map.lookup (j1, j2) m of
          Just a -> tell a >> return True
          _ -> return False

  runWriterT (allM (f sconf') (Set.toList $ split (confidentiality pNorm, confidentiality qNorm)) &&^
              allM (f sint') (Set.toList $ split (integrity pNorm, integrity qNorm))) >>= \case
    (True, a) -> return (True, a)
    (False, _) -> return (False, Set.empty)

split :: (J, J) -> Set (J, J)
split (j1, j2) = Set.fromList [(J (Set.singleton m1), J (Set.singleton m2))
                              | m1 <- List.concat [Set.toList (unJ j) | j <- Set.toList ((⊗) j1)],
                                m2 <- Set.toList (unJ j2) ]

{- Compute the expanded form of a delegation set -}
expand :: Set ((Principal, Principal), Assumptions) -> (Set ((J, M), Assumptions), Set ((J, M), Assumptions))
expand s = (expand' sconf, expand' sint)
  where
    s' = Set.map (first $ norm *** norm) s 
    sconf :: Set ((J, J), Assumptions)
    sconf = Set.map (first $ confidentiality *** confidentiality) s'
    sint :: Set ((J, J), Assumptions)
    sint = Set.map (first $ integrity *** integrity) s'

    expand' :: Set ((J, J), Assumptions) -> Set ((J, M), Assumptions)
    expand' = Set.foldr' (\((p, J q), a) ->
                            Set.union (Set.fromList [((p', q'), a)
                                                     | p' <- Set.toList ((⊗) p),
                                                       q' <- Set.toList q])) Set.empty

{- Not actually the powerset: We're removing the empty set -}
powerset :: Ord a => Set a -> Set (Set a)
powerset = Set.delete Set.empty .
           Set.fromList .
           List.map Set.fromList .
           filterM (const [True, False]) .
           Set.toList

{- For every (b /\ b ...) ≽ (b \/ b ...) we want a node for each non-empty
   subsequence of conjs and disjs -}
atomize :: Set ((J, M), Assumptions) -> Set ((J, J), Assumptions)
atomize s = Set.fromList
            [((J p', J (Set.singleton (M q'))), a) |
             ((J p, M q), a) <- Set.toList s, p' <- Set.toList (powerset p), q' <- Set.toList (powerset q)]

{- Compute transitive closure of a set -}
transitive :: Set ((J, J), Assumptions) -> Set ((J, J), Assumptions)
transitive s
  | s == s' = s
  | otherwise = transitive s'
  where s' = s `Set.union` Set.fromList [ ((a, c), ass1 `Set.union` ass2)
                                        | ((a, b), ass1) <- Set.toList s,
                                          ((b', c), ass2) <- Set.toList s,
                                          b == b']

{- Join of meets into meet of joins -}
(⊗) :: J -> Set J
(⊗) (J ms) = Set.fromList
             [J . Set.fromList $ map mkM ps |
              ps <- sequence [Set.toList bs | M bs <- Set.toList ms]]
  where mkM = M . Set.singleton

(⊳) :: MonadFLAMIO m => (Principal, Principal) -> FLAMIO a -> m a
(p, q) ⊳ x = liftFLAMIO (FLAMIO (local (over _1 $ inserts [(p, q)])
                                  (unFLAMIO x)))
  where inserts xs s = List.foldr Set.insert s xs

del :: (MonadFLAMIO m) => (Principal, Principal) -> m QueryResult
del (p, q) = do
  h <- getH
  strat <- getStrategy
  clr <- getClearance
  let run [] = return (False, Set.empty)
      run (stratClr : strat) =
        let f lab = do
              l <- liftLIO getLabel
              (b1, a1) <- incrD *> ((p, q) ⊳ (labelOf lab ⊔ l .⊑. clr) >>= lowerB') <* decrD
              (b2, a2) <- incrD *> ((p, q) ⊳ (labelOf lab .⊑. stratClr) >>= lowerB') <* decrD
              case (b1, b2) of
                (True, True) -> Just <$> ((,) <$> (p, q) ⊳ (unlabel lab) <*> pure ((a1 `Set.union` a2) \\ Set.singleton (p, q)))
                _ -> return Nothing
        in setFilterMapM f (unH h) >>= reach (p, q) >>= \case
             (True, a) -> return (True, a)
             (False, a) -> second (Set.union a) <$> run strat
  uncurry (flip liftB) <$> run (unStrategy strat)

assump :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
assump (p, q) = do
  assumptions <- getAssumptions
  let x = Set.foldr' f Set.empty assumptions
  r <- uncurry (flip liftB) <$> reach (p, q) x
  return r
  where f (p, q) = Set.insert ((p, q), Set.singleton (p, q))

distrL :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
distrL ((:→) (p1 :/\ p2), q) = incrD *> (((p1 →) /\ (p2 →)) .≽. q) <* decrD
distrL ((:→) (p1 :\/ p2), q) = incrD *> (((p1 →) \/ (p2 →)) .≽. q) <* decrD
distrL ((:←) (p1 :/\ p2), q) = incrD *> (((p1 ←) /\ (p2 ←)) .≽. q) <* decrD
distrL ((:←) (p1 :\/ p2), q) = incrD *> (((p1 ←) \/ (p2 ←)) .≽. q) <* decrD
distrL _ = return $ Failed Set.empty

distrR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
distrR (p, (:→) (q1 :/\ q2)) = incrD *> (p .≽. ((q1 →) /\ (q2 →))) <* decrD
distrR (p, (:→) (q1 :\/ q2)) = incrD *> (p .≽. ((q1 →) \/ (q2 →))) <* decrD
distrR (p, (:←) (q1 :/\ q2)) = incrD *> (p .≽. ((q1 ←) /\ (q2 ←))) <* decrD
distrR (p, (:←) (q1 :\/ q2)) = incrD *> (p .≽. ((q1 ←) \/ (q2 ←))) <* decrD
distrR _ = return $ Failed Set.empty

instance Binary s => Binary (Strategy s)

hasNames :: Principal -> Bool
hasNames (:⊤) = False
hasNames (:⊥) = False
hasNames (p1 :/\ p2) = hasNames p1 || hasNames p2
hasNames (p1 :\/ p2) = hasNames p1 || hasNames p2
hasNames (p1 ::: p2) = hasNames p1 || hasNames p2
hasNames (Name _) = True
hasNames ((:→) p) = hasNames p
hasNames ((:←) p) = hasNames p

lookupForwardCache :: MonadFLAMIO m => Principal -> (Principal, Principal) -> m (Maybe Bool)
lookupForwardCache n (p, q) = do
  Map.lookup n <$> getForwardCache >>= \case
    Just m -> return $ Map.lookup (p, q) m  
    Nothing -> return Nothing

updateForwardCache :: MonadFLAMIO m => Principal -> (Principal, Principal) -> Bool -> m ()
updateForwardCache n (p, q) b = liftFLAMIO $ FLAMIO $ modify $ f
  where f c = case Map.lookup n c of
                Just m -> Map.insert n (Map.insert (p, q) b m) c
                Nothing -> Map.singleton n (Map.singleton (p, q) b)

forward :: forall m . MonadFLAMIO m => (Principal, Principal) -> m QueryResult
forward (p, q)
  | hasNames p || hasNames q = do
    l <- getLabel
    useSockets $ \socks -> do
      ns <- mapMaybeM (\s -> do
              let n = channelLabel s
              canForwardTo n >>= \case
                False -> return Nothing
                True -> do
                  incrD *> ((p, q) ⊳ ((n →) .≽. (l →)) >>= lowerB') <* decrD >>= \case
                    (True, a) -> return $ Just (s, a \\ Set.singleton (p, q))
                    (False, _) -> return Nothing) socks
      run ns
  | otherwise = return $ Failed Set.empty
    where
      run :: [(LSocket, Assumptions)] -> m QueryResult
      run [] = return $ Failed Set.empty
      run ((s, a) : ns) = do
        let n = channelLabel s
        lookupForwardCache n (p, q) >>= \case
          Just b -> return $ liftB a b
          Nothing -> do
            strat <- getStrategy
            clr <- getClearance
            let ns' = List.map (\(s, _) -> channelLabel s) ns
            liftFLAMIO $ liftLIO $ liftIO $ send (sendChan s) (p, q, strat, clr : ns') FwdQuery
            liftFLAMIO (liftLIO $ liftIO $ recv (recvFwdResChan s)) >>= \case
              Just True -> do
                --updateForwardCache n (p, q) True
                return $ Success a
              r -> do
                --updateForwardCache n (p, q) False
                (^) <$> run ns <*> pure a

(.≽) :: MonadFLAMIO m => Principal -> Principal -> m QueryResult
p .≽ q =
  assump (p, q) <|||>
  bot_ (p, q) <|||>
  top_ (p, q) <|||>
  refl (p, q) <|||>
  del (p, q) <|||>
  distrL (p, q) <|||>
  distrR (p, q) <|||>
  proj (p, q) <|||>
  projR (p, q) <|||>
  own1 (p, q) <|||>
  own2 (p, q) <|||>
  conjR (p, q) <|||>
  disjL (p, q) <|||>
  disjR (p, q) <|||>
  conjL (p, q) <|||>
  forward (p, q)
  
(≽) :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal) => a -> b -> m Bool
p ≽ q =
  runReaderT (evalStateT (unAssumptionsT ((normalize (p %) .≽. normalize (q %)) >>= lowerB)) Map.empty) (Set.empty, Set.empty)
infix 6 ≽

instance SemiLattice Principal where
  p .⊔. q = normalize (((p /\ q) →) /\ ((p \/ q) ←))
  p .⊓. q = normalize (((p \/ q) →) /\ ((p /\ q) ←))

instance Label Principal where
  type C Principal = MonadFLAMIO
  p ⊑ q = ((q →) /\ (p ←)) ≽ ((p →) /\ (q ←))

(.⊑.) :: MonadFLAMIO m => Principal -> Principal -> m QueryResult
p .⊑. q = normalize ((q →) /\ (p ←)) .≽. normalize ((p →) /\ (q ←))
  
mSingleton :: L -> M
mSingleton = M . Set.singleton

jSingleton :: L -> J
jSingleton = J . Set.singleton . mSingleton

mTop :: M
mTop = mSingleton T

mBot :: M
mBot = mSingleton B

jTop :: J
jTop = jSingleton T

jBot :: J
jBot = jSingleton B

norm :: Principal -> JNF
norm (:⊤) =
  JNF { confidentiality = jTop, integrity = jTop }
norm (:⊥) =
  JNF { confidentiality = jBot, integrity = jBot }
norm (Name x) =
  JNF { confidentiality = jSingleton (N x),
        integrity = jSingleton (N x) }
norm (p1 :/\ p2) =
  conj (norm p1) (norm p2)
norm (p1 :\/ p2) =
  disj (norm p1) (norm p2)
norm ((:→) p) =
  JNF { confidentiality = jNormConf p, integrity = jBot }
norm ((:←) p) =
  JNF { confidentiality = jBot, integrity = jNormInt p }
norm (p1 ::: p2) = owner (norm p1) (norm p2)

reify :: JNF -> Principal
reify (JNF c i) = ((reifyJ c) →) :/\ ((reifyJ i) ←)
  where
 reifyJ :: J -> Principal
 reifyJ (J (listview -> [m])) = reifyM m
 reifyJ (J (setview -> Just (m, ms))) = reifyM m :/\ reifyJ (J ms)
 
 reifyM :: M -> Principal
 reifyM (M (listview -> [b])) = reifyBase b
 reifyM (M (setview -> Just (b, bs))) = reifyBase b :\/ reifyM (M bs)

 reifyBase :: L -> Principal
 reifyBase B = (:⊥)
 reifyBase T = (:⊤)
 reifyBase (N s) = Name s
 reifyBase (b1 :.: b2) = (b1 %) ::: (b2 %)

normalize :: Principal -> Principal
normalize = reify . norm

mergeB :: L -> L -> Either L L
mergeB T r = Left r
mergeB l T = Left l
mergeB B _ = Left B
mergeB _ B = Left B
mergeB l r
  | l == r = Left l
mergeB l _ = Right l

mergeM :: M -> M -> Either M M
mergeM (M (listview -> [T])) _ = Left (M (Set.singleton T))
mergeM _ (M (listview -> [T])) = Left (M (Set.singleton T))
mergeM (M ms) r
  | B `Set.member` ms = Left r
mergeM l (M ms)
  | B `Set.member` ms = Left l
mergeM (M (listview -> [l])) (M rs) | elem l rs = Left (M (Set.singleton l))
mergeM (M ls) (M (listview -> [r])) | elem r ls = Left (M (Set.singleton r))
mergeM l r | l == r = Left l
mergeM l _ = Right l

zeroM :: M -> Bool
zeroM (M (setview -> Nothing)) = True
zeroM (M bs) = B `Set.member` bs

mkNonEmpty :: J -> J
mkNonEmpty (J (setview -> Nothing)) = J (Set.singleton (M (Set.singleton B)))
mkNonEmpty s      = s

mergeWith :: (a -> a -> Either a a) -> [a] -> [a]
mergeWith _ []      = []
mergeWith op (f:fs) = case partitionEithers $ map (`op` f) fs of
                        ([], _)              -> f : mergeWith op fs
                        (updated, untouched) -> mergeWith op (updated ++ untouched)

jSimplify :: J -> J
jSimplify = repeatF go
  where
    go = mkNonEmpty
       . J
       . Set.fromList
       . List.sort . filter (not . zeroM)
       . mergeWith mergeM
       . map (M . Set.fromList . List.sort . mergeWith mergeB . Set.toList . unM)
       . Set.toList
       . unJ

    repeatF f x =
      let x' = f x
      in if x' == x
         then x
         else repeatF f x'

jNormConf :: Principal -> J
jNormConf (:⊤) = jTop
jNormConf (:⊥) = jBot
jNormConf (Name x) = jSingleton (N x)
jNormConf (p1 :/\ p2) =
  jNormConf p1 `jConj` jNormConf p2
jNormConf (p1 :\/ p2) =
  jNormConf p1 `jDisj` jNormConf p2
jNormConf ((:→) p) = jNormConf p
jNormConf ((:←) _) = jBot
jNormConf (p1 ::: p2) = confidentiality $ normOwnsJ (norm p1) (jNormConf p2)

jNormInt :: Principal -> J
jNormInt (:⊤) = jTop
jNormInt (:⊥) = jBot
jNormInt (Name x) = jSingleton (N x)
jNormInt (p1 :/\ p2) =
  jNormInt p1 `jConj` jNormInt p2
jNormInt (p1 :\/ p2) =
  jNormInt p1 `jDisj` jNormInt p2
jNormInt ((:→) p) = jBot
jNormInt ((:←) p) = jNormInt p
jNormInt (p1 ::: p2) = integrity $ normOwnsJ (norm p1) (jNormInt p2)

jConj :: J -> J -> J
jConj (J ms1) (J ms2) = jSimplify (J $ ms1 `Set.union` ms2)

jDisj :: J -> J -> J
jDisj (J ms1) (J ms2) =
  jSimplify
  . J
  . Set.fromList
  $ concatMap
  (zipWith (\(M p1) (M p2) ->
               M (p1 `Set.union` p2)) (Set.toList ms1) . repeat)
  (Set.toList ms2)

conj :: JNF -> JNF -> JNF
conj (JNF c1 i1) (JNF c2 i2) =
  JNF { confidentiality = jConj c1 c2,
        integrity = jConj i1 i2 }

disj :: JNF -> JNF -> JNF
disj (JNF c1 i1) (JNF c2 i2) =
  JNF { confidentiality = jDisj c1 c2,
        integrity = jDisj i1 i2 }

owner :: JNF -> JNF -> JNF
owner p (JNF qc qi) =
  conj JNF {confidentiality = jNormConf ((%) (normOwnsJ p qc)), integrity = jBot}
       JNF {confidentiality = jBot, integrity = jNormInt ((%) (normOwnsJ p qi)) }

normOwnsJ :: JNF -> J -> JNF
normOwnsJ p (J (listview -> [m])) = normOwnsM p m
normOwnsJ p (J (setview -> Just (m, ms))) = conj (normOwnsM p m) (normOwnsJ p (J ms))

normOwnsM :: JNF -> M -> JNF
normOwnsM p (M (listview -> [b])) = normOwnsL p b
normOwnsM p (M (setview -> Just (b, bs))) = disj (normOwnsL p b) (normOwnsM p (M bs))

normOwnsL :: JNF -> L -> JNF
normOwnsL JNF { confidentiality = pc, integrity = pi } q =
  JNF { confidentiality = normOwnsJL pc q, integrity = normOwnsJL pi q }

normOwnsJL :: J -> L -> J
normOwnsJL (J (listview -> [m])) q = J . Set.singleton $ normOwnsML m q
normOwnsJL (J (setview -> Just (m, ms))) q = J (normOwnsML m q `Set.insert` ms')
  where J ms' = normOwnsJL (J ms) q

normOwnsML :: M -> L -> M
normOwnsML (M (listview -> [b])) q = M . Set.singleton $ normOwnsLL b q
normOwnsML (M (setview -> Just (b, bs))) q = M (normOwnsLL b q `Set.insert` bs')
  where M bs' = normOwnsML (M bs) q

normOwnsLL :: L -> L -> L
normOwnsLL p (N q) = p :.: N q
normOwnsLL p T = p :.: T
normOwnsLL p B = B
normOwnsLL p (q1 :.: q2) = p :.: (q1 :.: q2)

instance ToLabel JNF Principal where
  (%) x = ((confidentiality x) →) :/\ ((integrity x) ←)

instance ToLabel [Char] Principal where
  (%) = Name

instance ToLabel J Principal where
  (%) (J (listview -> [m])) = (%) m
  (%) (J (setview -> Just (m, ms))) = (%) m :/\ (%) (J ms)

instance ToLabel M Principal where
  (%) (M (listview -> [l])) = (%) l
  (%) (M (setview -> Just (l, ls))) = (%) l :\/ (%) (M ls)

instance ToLabel L Principal where
  (%) (N s) = (%) s
  (%) T = (:⊤)
  (%) B = (:⊥)
  (%) (p :.: q) = (%) p ::: (%) q

(/\) :: (ToLabel a Principal, ToLabel b Principal) => a -> b -> Principal
a /\ b = (a %) :/\ (b %)
infixr 8 /\

(∧) :: (ToLabel a Principal, ToLabel b Principal) => a -> b -> Principal
a ∧ b = (a %) :/\ (b %)
infixr 8 ∧
  
(\/) :: (ToLabel a Principal, ToLabel b Principal) => a -> b -> Principal
a \/ b = (a %) :\/ (b %)
infixr 7 \/

(∨) :: (ToLabel a Principal, ToLabel b Principal) => a -> b -> Principal
a ∨ b = (a %) :\/ (b %)
infixr 7 ∨
  
(→) :: (ToLabel a Principal) => a -> Principal
(→) a = case (a %) of
          (:→) p -> (:→) p
          p -> (:→) p

(←) :: (ToLabel a Principal) => a -> Principal
(←) a = case (a %) of
          (:←) p -> (:←) p
          p -> (:←) p

(.:) :: (ToLabel a Principal, ToLabel b Principal) => a -> b -> Principal
a .: b = (a %) ::: (b %)

type FLAM = Principal

(⊥) :: Principal
(⊥) = (:⊥)

(⊤) :: Principal
(⊤) = (:⊤)

bot :: Principal
bot = (:→) (:⊥) :/\ (:←) (:⊤)

top :: Principal
top = (:→) (:⊤) :/\ (:←) (:⊥)

class RPCInvokable t

class Typeable f => Curryable f where
  c :: (Typeable m, MonadFLAMIO m) => f -> [Dynamic] -> m (Maybe Dynamic)

class Typeable f => Curryable' (isArrow :: Bool) f where
  c' :: (Typeable m, MonadFLAMIO m) => Proxy isArrow -> f -> [Dynamic] -> m (Maybe Dynamic)

type family IsArrow a where
  IsArrow (a -> b) = 'True
  IsArrow _ = 'False

instance (IsArrow f ~ isArrow, Typeable f, Curryable' isArrow f) => Curryable f where
  c f xs = c' (Proxy :: Proxy isArrow) f xs

data RPCInvokableExt = forall t a b . (RPCInvokable t, Typeable t, Curryable t) => RPCInvokableExt t

data FLAMIOSt = FLAMIOSt { _cache :: Cache,
                           _sockets :: MVar [LSocket],
                           _exports :: Map String RPCInvokableExt,
                           _hPtr :: MVar H,
                           _depth :: Int }

cache :: Lens' FLAMIOSt Cache
cache = lens _cache (\st c -> st { _cache = c })

sockets :: Lens' FLAMIOSt (MVar [LSocket])
sockets = lens _sockets (\st s -> st { _sockets = s })

exports :: Lens' FLAMIOSt (Map String RPCInvokableExt)
exports = lens _exports (\st e -> st { _exports = e })

hPtr :: Lens' FLAMIOSt (MVar H)
hPtr = lens _hPtr (\st h -> st { _hPtr = h })

depth :: Lens' FLAMIOSt Int
depth = lens _depth (\st d -> st { _depth = d })

getH :: MonadFLAMIO m => m H
getH = do
  mvar <- getHPtr
  liftFLAMIO $ liftLIO $ liftIO $ readMVar mvar

insertInHPtr :: MonadFLAMIO m => Labeled Principal (Principal, Principal) -> m ()
insertInHPtr lab = do
  h <- getHPtr
  liftFLAMIO $ liftLIO $ liftIO $ modifyMVar_ h (return . H . Set.insert lab . unH)

removeFromHPtr :: MonadFLAMIO m => Labeled Principal (Principal, Principal) -> m ()
removeFromHPtr lab = do
  h <- getHPtr
  liftFLAMIO $ liftLIO $ liftIO $ modifyMVar_ h (return . H . Set.delete lab . unH)

getSockets :: MonadFLAMIO m => m (MVar [LSocket])
getSockets = liftFLAMIO $ FLAMIO $ lift $ gets (view sockets)

useSockets :: MonadFLAMIO m => ([LSocket] -> m a) -> m a
useSockets f = do
  mvar <- getSockets
  socks <- liftFLAMIO $ liftLIO $ liftIO $ readMVar mvar
  x <- f socks
  return x

putSocket :: MonadFLAMIO m => LSocket -> m ()
putSocket s = do
  mvar <- getSockets
  socks <- liftFLAMIO $ liftLIO $ liftIO $ takeMVar mvar
  liftFLAMIO $ liftLIO $ liftIO $ putMVar mvar (s : socks)

removeSocket :: MonadFLAMIO m => LSocket -> m ()
removeSocket s = do
  mvar <- getSockets
  socks <- liftFLAMIO $ liftLIO $ liftIO $ takeMVar mvar
  liftFLAMIO $ liftLIO $ liftIO $ putMVar mvar (List.delete s socks)

export :: (MonadFLAMIO m, RPCInvokable t, Curryable t) => String -> t -> m ()
export s f = liftFLAMIO $ FLAMIO $ lift $ modify $ over exports $
               Map.insert s (RPCInvokableExt f)

lookupRPC :: MonadFLAMIO m => String -> m (Maybe RPCInvokableExt)
lookupRPC s = Map.lookup s <$> liftFLAMIO (FLAMIO $ lift (gets (view exports)))

getHPtr :: MonadFLAMIO m => m (MVar H)
getHPtr = liftFLAMIO $ FLAMIO $ lift $ gets (view hPtr)

instance MonadLIO FLAM FLAMIO where
  liftLIO = FLAMIO . liftLIO

(∇) :: (ToLabel a Principal) => a -> Principal
(∇) a = normalize $ (confidentiality p' ←) /\ (integrity p' ←)
  where p' = norm (a %)

addDelegate :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal, ToLabel c Principal) =>
               a -> b -> c -> m ()
addDelegate p q l = do
  lbl <- getLabel
  (,) <$> lbl ≽ (∇) q <*> (∇) (p →) ≽ (∇) (q →) >>= \case
    (True, True) -> do
      lab <- label l (normalize (p %), normalize (q %))
      liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
      insertInHPtr lab
    (False, _) -> error $ "IFC violation (addDelegate 1): " ++ show lbl ++ " ≽ " ++ show ((∇) q)
    (_, False) -> error $ "IFC violation (addDelegate 2): " ++ show ((∇) (p →)) ++ " ≽ " ++ show ((∇) (q →))

removeDelegate :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal, ToLabel c Principal) =>
                  a -> b -> c -> m ()
removeDelegate p q l = do
  lab <- label l (normalize (p %), normalize (q %))
  liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
  removeFromHPtr lab

withStrategy :: (MonadFLAMIO m, ToLabel b Principal) => [b] -> m a -> m a
withStrategy newStrat m = do
  liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
  oldStrat <- liftLIO $ gets $ view _2
  liftLIO $ modify $ (_2 .~ Strategy (fmap (normalize . (%)) newStrat))
  x <- m
  liftLIO $ modify $ (_2 .~ oldStrat)
  return x

noStrategy :: Strategy Principal
noStrategy = Strategy []

newScope :: (MonadFLAMIO m) => m a -> m a
newScope m = do
  mvar <- getHPtr
  h <- liftFLAMIO $ liftLIO $ liftIO $ readMVar mvar
  x <- m
  liftFLAMIO $ liftLIO $ liftIO $ tryTakeMVar mvar
  liftFLAMIO $ liftLIO $ liftIO $ putMVar mvar h
  return x

noForwardTo :: (MonadFLAMIO m) => Set Principal -> FLAMIO a -> m a
noForwardTo dontfwdto x = liftFLAMIO (FLAMIO $ local (over _2 $ const dontfwdto) (unFLAMIO x))

runFLAMWithCache :: ToLabel b Principal => b -> Cache -> FLAMIO a -> MVar H -> MVar [LSocket] -> IO a
runFLAMWithCache clr c m h socks = do
  evalStateT
    (unLIO $ evalStateT
      (runReaderT
        (evalStateT
          (unAssumptionsT $ unFLAMIO m)
          Map.empty)
        (Set.empty, Set.empty))
      (FLAMIOSt c socks Map.empty h 0))
    (BoundedLabel { _cur = bot, _clearance = (clr →) ∧ ((⊥) ←) }, noStrategy)

runFLAM :: ToLabel b Principal => b -> FLAMIO a -> IO a
runFLAM clr m = do
  h <- newMVar (H Set.empty)
  socks <- newMVar []
  runFLAMWithCache clr emptyCache m h socks

runFLAMWithMVars :: FLAMIO a -> MVar H -> MVar [LSocket] -> StateT (BoundedLabel FLAM, Strategy FLAM) IO a
runFLAMWithMVars m h socks =
  (unLIO $ evalStateT
    (runReaderT
      (evalStateT
        (unAssumptionsT $ unFLAMIO m)
        Map.empty)
      (Set.empty, Set.empty))
    (FLAMIOSt emptyCache socks Map.empty h 0))

instance MonadFLAMIO FLAMIO where
  liftFLAMIO = id

instance MonadFLAMIO m => MonadFLAMIO (StateT s m) where
 liftFLAMIO = lift . liftFLAMIO

instance MonadFLAMIO m => MonadFLAMIO (ReaderT r m) where
  liftFLAMIO = lift . liftFLAMIO

instance MonadFLAMIO m => MonadFLAMIO (AssumptionsT m) where
  liftFLAMIO = lift . liftFLAMIO

instance ForkableMonad m => ForkableMonad (AssumptionsT m) where
  forkIO (AssumptionsT m) = AssumptionsT $ forkIO m
  
instance ForkableMonad FLAMIO where
  forkIO (FLAMIO m) = FLAMIO $ forkIO m

instance MonadFix m => MonadFix (AssumptionsT m) where
  mfix f = AssumptionsT $ mfix $ \a -> unAssumptionsT (f a)
  
instance MonadFix FLAMIO where
  mfix f = FLAMIO $ mfix $ \a -> unFLAMIO (f a)

forkFinally :: (ForkableMonad m, MonadMask m) => m a -> (Either SomeException a -> m ()) -> m ThreadId
forkFinally action and_then =
  mask $ \restore ->
    forkIO $ try (restore action) >>= and_then
