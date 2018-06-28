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
import Data.Maybe
import qualified Data.POMap.Strict as POMap
import Data.POMap.Strict(POMap)
import Algebra.PartialOrd
import Algebra.Lattice.Op
import Data.Foldable

import Data.Proxy

{- For networking -}
import Control.Monad.Catch
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net

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
  deriving (Eq, Ord)

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
  deriving (Ord, Eq, Show)

data L
  = N !String
  | T
  | B
  | !L :.: !L
  deriving (Eq, Ord, Show)

newtype M = M { unM :: Set L } -- L₁ \/ L₂ \/ ... \/ Lₙ
  deriving (Eq, Ord, Show)

newtype J = J { unJ :: Set M } -- M₁ /\ M₂ /\ ... /\ Mₙ
  deriving (Eq, Ord, Show)

data JNF = JNF { confidentiality :: !J, integrity :: !J }
  deriving (Show, Eq, Ord)

data ProgressCondition
  = ActsFor !Principal !Principal
  | Conj !(ProgressCondition) !(ProgressCondition)
  | Disj !(ProgressCondition) !(ProgressCondition)
  | TrueCondition
  | FalseCondition
  deriving Eq

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

type Assumptions = Map Int (Set (Principal, Principal))
newtype StepIndexT m a = StepIndexT { unStepIndexT :: ReaderT (Int, Assumptions) m a }
  deriving (Functor, Applicative, Monad, MonadReader (Int, Assumptions))

instance MonadState s m => MonadState s (StepIndexT m) where
  get = StepIndexT get
  put = StepIndexT . put

instance (PartialOrd a, PartialOrd b, PartialOrd c) => PartialOrd (a, b, c) where
  (a1, b1, c1) `leq` (a2, b2, c2) = a1 `leq` a2 && b1 `leq` b2 && c1 `leq` c2

instance PartialOrd Principal where
  x `leq` y = x <= y

instance PartialOrd H where
  H x `leq` H y = x `leq` y

type SureCache = Map (Principal, Principal) (Map Int (Map (Principal, Principal) Principal))
type UnsureCache = Map Int (Map (Principal, Principal) (ProgressCondition))

type ReachabilityCache = Map (Set ((Principal, Principal), Assumptions)) ((Set ((J, J), Assumptions), Set ((J, J), Assumptions)))
type ProvedCache = POMap (Assumptions, Strategy Principal, H) SureCache
type PrunedCache = Map Assumptions (Map (Principal, Principal) UnsureCache)
type FailedCache = POMap (Op (Assumptions, Strategy Principal, H)) SureCache
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
Failed a1 ^ a2 = Failed (Map.union a1 a2)
Success a1 ^ a2 = Success (Map.union a1 a2)
Pruned pc a1 ^ a2 = Pruned pc (Map.union a1 a2)

liftB :: Assumptions -> Bool -> QueryResult
liftB a True = Success a
liftB a False = Failed a

lowerB' :: MonadFLAMIO m => Int -> QueryResult -> m (Bool, Assumptions)
lowerB' idx (Success a) = return (True, a)
lowerB' idx (Failed a) = return (False, a)
lowerB' idx (Pruned pc a) =
  isTrue a idx pc >>= \case
    Just b -> return (b, a)
    Nothing -> return (False, a)

lowerB :: MonadFLAMIO m => Int -> QueryResult -> m Bool
lowerB idx r = fst <$> lowerB' idx r
  
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
        Success a2 -> return $ Pruned pc1 (a1 `Map.union` a2)
        Failed a2 -> return $ Failed (a1 `Map.union` a2)
        Pruned pc2 a2 -> return $ Pruned (pc1 `Conj` pc2) (a1 `Map.union` a2)
infixr 8 <&&&>

(<|||>) :: (Monad m) => m QueryResult -> m QueryResult -> m QueryResult
(<|||>) m1 m2 =
  m1 >>= \case
    Success a -> return $ Success a
    Failed a -> (^) <$> m2 <*> pure a
    Pruned pc1 a1 ->
      m2 >>= \case
        Success a2 -> return $ Success (a1 `Map.union` a2)
        Failed a2 -> return $ Pruned pc1 (a1 `Map.union` a2)
        Pruned pc2 a2 -> return $ Pruned (pc1 `Disj` pc2) (a1 `Map.union` a2)
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

(⇒) :: Assumptions -> Assumptions -> Bool
(⇒) = flip Map.isSubmapOf

isTrue :: MonadFLAMIO m => Assumptions -> Int -> ProgressCondition -> m (Maybe Bool)
isTrue a idx (ActsFor p q) = do
  (_, assumptions) <- liftFLAMIO $ FLAMIO $ ask
  let assumptions' = Map.takeWhileAntitone (<= idx) assumptions
  -- TODO: This mapping is weird.
  -- Also I don't think we should be ignoring the assumptions coming out here?
  (b, _) <- reach (p, q) (Set.map (, Map.empty) (Set.unions . Map.elems $ assumptions'))
  case b of
    True -> return $ Just (a ⇒ assumptions')
    False -> return Nothing
isTrue a idx (Conj pc1 pc2) =
  isTrue a idx pc1 >>= \case
    Just True -> isTrue a idx pc2
    Just False -> return $ Just False
    Nothing -> return $ Nothing
isTrue a idx (Disj pc1 pc2) =
 isTrue a idx pc1 >>= \case
   Just True -> return $ Just True
   Just False -> isTrue a idx pc1
   Nothing -> return $ Nothing
isTrue _ _ TrueCondition = return $ Just True
isTrue _ _ FalseCondition = return $ Just False

isFalse :: MonadFLAMIO m => Assumptions -> Int -> ProgressCondition -> m (Maybe Bool)
isFalse a idx pc =
  isTrue a idx pc >>= \case
    Just b -> return $ Just $ not b
    Nothing -> return $ Nothing

mapMaybeKeepM :: (Ord k, Monad m) => (a -> m (Maybe b)) -> Map k a -> m (Map k a, Map k b)
mapMaybeKeepM _ (mapview -> Nothing) = return (Map.empty, Map.empty)
mapMaybeKeepM f (mapview -> Just ((k, a), m)) = do
  (m1, m2) <- mapMaybeKeepM f m
  f a >>= \case
    Just b -> return (m1, Map.insert k b m2)
    Nothing -> return (Map.insert k a m1, m2)

alterSure :: (Maybe (Map Int (Map (Principal, Principal) Principal)) -> Maybe (Map Int (Map (Principal, Principal) Principal))) ->
             Principal -> Principal ->
             Maybe SureCache -> Maybe SureCache
alterSure f cur clr Nothing = Map.singleton (cur, clr) <$> f Nothing
alterSure f cur clr (Just m) = Map.insert (cur, clr) <$> f (Map.lookup (cur, clr) m) <*> pure m

insert p q idx cur Nothing = Map.singleton idx (Map.singleton (p, q) cur)
insert p q idx cur (Just map) =
  case Map.lookup idx map of
    Just m -> Map.insert idx (Map.insert (p, q) cur m) map
    Nothing -> Map.insert idx (Map.singleton (p, q) cur) map

updatePruned :: (Monad m) => Int -> Principal -> Principal -> ProgressCondition ->
                (Int -> ProgressCondition -> m (Maybe Bool)) -> ProgressCondition ->
                m (Maybe ProgressCondition)
updatePruned idx p q rep cond progCond = do
          let progCond' = substitute (Pattern (ActsFor p q)) (Replacement rep) (Original progCond)
          cond idx progCond' >>= \case
            Just True -> do
              return Nothing
            Just False -> do
              return $ Just progCond'
            Nothing -> do
              return $ Just progCond'

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

update :: forall m . MonadFLAMIO m => (Principal, Principal) -> Int -> (Principal, Principal) -> QueryResult -> m ()
update (cur, clr) idx (p, q) (Success a) = do
  cur' <- liftLIO getLabel
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  liftFLAMIO $ modifyCache $ over provedCache $ adjustPOMapGT (adjustOrInsert (insert p q idx cur') (cur, clr)) (a, strat, h)
  liftFLAMIO $ modifyCache $ over provedCache $ POMap.alter (alterSure (Just . insert p q idx cur') cur clr) (a, strat, h)
  liftFLAMIO $ modifyCache $ over prunedCache $ adjustMapGE (Map.adjust (Map.mapWithKey delete) (cur, clr)) a
  prunedmap <- Map.lookup a <$> liftFLAMIO (getsCache (view prunedCache)) >>= \case
    Just prunedmap ->
      case Map.lookup (cur, clr) prunedmap of
        Just pm -> mapMapWithKeyM f pm
          where f idx' =
                  if idx <= idx' then
                    mapMapMaybeM (updatePruned idx p q TrueCondition (isTrue a)) --TODO: Is a correct here?
                  else return
        Nothing -> return Map.empty
    Nothing -> return Map.empty
  liftFLAMIO $ modifyCache $ over prunedCache $
    Map.alter (Just . \case
                  Just m -> Map.insert (cur, clr) prunedmap m
                  Nothing -> Map.singleton (cur, clr) prunedmap
              ) a
  where delete idx' m = if idx <= idx' then Map.delete (p, q) m else m
  
update (cur, clr) idx (p, q) (Pruned pc a) = do
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.adjust (Map.alter (Just . insert p q idx pc) (cur, clr)) a
  prunedmap <- Map.lookup a <$> liftFLAMIO (getsCache (view prunedCache)) >>= \case
    Just prunedmap ->
      case Map.lookup (cur, clr) prunedmap of
        Just pm -> return $ Map.mapWithKey (\idx' -> if idx <= idx' then Map.map (updatePruned idx) else id) pm
        Nothing -> return Map.empty
    Nothing -> return Map.empty
  liftFLAMIO $ modifyCache $ over prunedCache $
    Map.alter (Just . \case
                  Just m -> Map.insert (cur, clr) prunedmap m
                  Nothing -> Map.singleton (cur, clr) prunedmap
              ) a
  where updatePruned :: Int -> ProgressCondition -> ProgressCondition
        updatePruned idx = substitute (Pattern (ActsFor p q)) (Replacement pc) . Original
        
update (cur, clr) idx (p, q) (Failed a) = do
  cur' <- liftLIO getLabel
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  liftFLAMIO $ modifyCache $ over failedCache $ adjustPOMapGT (adjustOrInsert (insert p q idx cur') (cur, clr)) (Op (a, strat, h))
  liftFLAMIO $ modifyCache $ over failedCache $ POMap.alter (alterSure (Just . insert p q idx cur') cur clr) (Op (a, strat, h))
  liftFLAMIO $ modifyCache $ over prunedCache $ adjustMapLE (Map.update (Just . Map.mapWithKey delete) (cur, clr)) a

  pruned <- Map.takeWhileAntitone (`leq` a) <$> (liftFLAMIO $ getsCache $ view prunedCache)
  forM_ (Map.toList pruned) $ \(assumptions, prunedmap) -> do
    case Map.lookup (cur, clr) prunedmap of
      Just prunedmap1 ->
        mapM_ (\(idx', m) -> do
                  (new', pruned') <- mapMaybeKeepM (updatePruned idx p q FalseCondition (isFalse a)) m -- TODO: Is a correct here?
                  mapM_ (\(p, q) -> update (cur, clr) idx' (p, q) (Failed a)) (Map.keys m) -- TODO: Is a correct here?
                  let adjust :: Maybe UnsureCache -> UnsureCache
                      adjust Nothing = Map.singleton idx' pruned'
                      adjust (Just m) = Map.insert idx' pruned' m
                  liftFLAMIO $ modifyCache $ over prunedCache $ Map.adjust (adjustOrInsert adjust (cur, clr)) assumptions
              ) (Map.toList prunedmap1')
        where prunedmap1' = Map.filterWithKey (\idx' -> if idx <= idx' then const True else const False) prunedmap1
      Nothing -> return ()
     where delete idx' m = if idx <= idx' then Map.delete (p, q) m else m
 
searchSureCache :: (Principal, Principal) -> Int ->
                   Map Int (Map (Principal, Principal) Principal) -> Maybe Principal
searchSureCache (p, q) idx m =
  let m' = Map.takeWhileAntitone (<= idx) m
  in Map.lookup (p, q) (Map.unions $ Map.elems m')
  
searchSurePOMap :: (Principal, Principal) -> (Principal, Principal) -> Int ->
                   POMap (Assumptions, Strategy Principal, H) SureCache -> Maybe (Principal, Assumptions)
searchSurePOMap (cur, clr) (p, q) idx m = search (POMap.toList m)
  where search [] = Nothing
        search (((a, _, _), c) : cs) =
          case Map.lookup (cur, clr) c of
          Just m -> case searchSureCache (p, q) idx m of
                      Just p -> Just (p, a)
                      Nothing -> search cs
          Nothing -> search cs

searchSurePOMapOp :: (Principal, Principal) -> (Principal, Principal) -> Int ->
                     POMap (Op (Assumptions, Strategy Principal, H)) SureCache -> Maybe (Principal, Assumptions)
searchSurePOMapOp (cur, clr) (p, q) idx m = search (POMap.toList m)
  where search [] = Nothing
        search ((Op (a, _, _), c) : cs) =
          case Map.lookup (cur, clr) c of
          Just m -> case searchSureCache (p, q) idx m of
                      Just p -> Just (p, a)
                      Nothing -> search cs
          Nothing -> search cs

searchFailedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (Principal, Assumptions))
searchFailedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO getCache
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  (idx, assumptions) <- liftFLAMIO $ FLAMIO ask
  let failedcache = POMap.takeWhileAntitone (`leq` Op (assumptions, strat, h)) (view failedCache cache)
  return $ searchSurePOMapOp (cur, clr) (p, q) idx failedcache
  
searchProvedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (Principal, Assumptions))
searchProvedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO $ getCache
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  (idx, assumptions) <- liftFLAMIO $ FLAMIO ask
  let provedcache = POMap.takeWhileAntitone (`leq` (assumptions, strat, h)) (view provedCache cache)
  return $ searchSurePOMap (cur, clr) (p, q) idx provedcache
  
data CacheSearchResult
  = ProvedResult !Principal !Assumptions
  | FailedResult !Principal !Assumptions
  | PrunedResult !ProgressCondition !Assumptions

searchPrunedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (ProgressCondition, Assumptions))
searchPrunedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO getCache
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  (idx, assumptions) <- liftFLAMIO $ FLAMIO ask
  case Map.lookup assumptions (view prunedCache cache) of
    Just uc ->
      case Map.lookup (cur, clr) uc of
        Just uc ->
          let uc' = Map.unions $ Map.elems $ Map.takeWhileAntitone (<= idx) uc
          in return ((,) <$> Map.lookup (p, q) uc' <*> pure assumptions)
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

instance MonadLIO s l m => MonadLIO s l (StepIndexT m) where
  liftLIO = lift . liftLIO
  
instance MonadTrans StepIndexT where
  lift = StepIndexT . lift 

withLöb :: MonadFLAMIO m => (Principal, Principal) -> FLAMIO a -> m a
withLöb (p, q) m = do
  (idx, _) <- liftFLAMIO $ FLAMIO ask
  liftFLAMIO $ FLAMIO $ local (second $ adjustOrInsert insert (idx + 1)) (unFLAMIO m)
  where insert Nothing = Set.singleton (normalize p, normalize q)
        insert (Just s) = Set.insert (normalize p, normalize q) s

(.≽.) :: MonadFLAMIO m => Principal -> Principal -> m QueryResult
p .≽. q = do
  curLab <- liftLIO getLabel
  clrLab <- liftLIO getClearance
  (idx, _) <- liftFLAMIO $ FLAMIO ask
  if idx > 3 then return $ Failed Map.empty
  else do
    x <- searchcache (curLab, clrLab) (p, q)
    case x of
      Just (ProvedResult cur' a) -> do
        liftLIO $ modify $ (_1 . cur) .~ cur'
        return $ Success a
      Just (FailedResult cur' a) -> do
        liftLIO $ modify $ (_1 . cur) .~ cur'
        return $ Failed a
      Just (PrunedResult pc a) -> do
        return $ Pruned pc a
      Nothing -> do
        update (curLab, clrLab) idx (p, q) (Pruned (ActsFor p q) Map.empty)
        r <- withLöb (p, q) (p .≽ q)
        update (curLab, clrLab) idx (p, q) r
        return r

bot_ :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
bot_ (_, (:⊥)) = return $ Success Map.empty
bot_ (_, (((:→) (:⊥)) :/\ ((:←) (:⊥)))) = return $ Success Map.empty
bot_ _ = return $ Failed Map.empty

top_ :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
top_ ((:⊤), _) = return $ Success Map.empty
top_ ((((:→) (:⊤)) :/\ ((:←) (:⊤))), _) = return $ Success Map.empty
top_ _ = return $ Failed Map.empty

refl :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
refl (p, q) | p == q = return $ Success Map.empty
refl _ = return $ Failed Map.empty

proj :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
proj ((:→) p, (:→) q) = p .≽. q
proj ((:←) p, (:←) q) = p .≽. q
proj _ = return $ Failed Map.empty

projR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
projR (p, (:←) q) | p == q = return $ Success Map.empty
projR (p, (:→) q) | p == q = return $ Success Map.empty
projR _ = return $ Failed Map.empty

own1 :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
own1 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. p'
own1 _ = return $ Failed Map.empty

own2 :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
own2 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. (o' ::: p')
own2 _ = return $ Failed Map.empty

conjL :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
conjL (p1 :/\ p2, p) = p1 .≽. p <|||> p2 .≽. p
conjL _ = return $ Failed Map.empty

conjR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
conjR (p, p1 :/\ p2) = p .≽. p1 <&&&> p .≽. p2
conjR _ = return $ Failed Map.empty

disjL :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
disjL (p1 :\/ p2, p) = p1 .≽. p <&&&> p2 .≽. p
disjL _ = return $ Failed Map.empty

disjR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
disjR (p, p1 :\/ p2) = p .≽. p1 <|||> p .≽. p2
disjR _ = return $ Failed Map.empty

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
  case (Map.lookup (confidentiality pNorm, confidentiality qNorm) sconf',
        Map.lookup (integrity pNorm, integrity qNorm) sint') of
    (Just a1, Just a2) -> return (True, a1 `Map.union` a2)
    _ -> return (False, Map.empty)
        
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
  where s' = s `Set.union` Set.fromList [((a, c), ass1 `Map.union` ass2)
                                        | ((a, b), ass1) <- Set.toList s,
                                          ((b', c), ass2) <- Set.toList s,
                                          b == b']

{- Join of meets into meet of joins -}
(⊗) :: J -> Set J
(⊗) (J ms) = Set.fromList
             [J . Set.fromList $ map mkM ps |
              ps <- sequence [Set.toList bs | M bs <- Set.toList ms]]
  where mkM = M . Set.singleton

class (MonadLIO H Principal m) => MonadFLAMIO m where
  liftFLAMIO :: FLAMIO a -> m a

instance HasCache c m => HasCache c (StateT s m) where
  getCache = StateT $ \s -> (,) <$> getCache <*> pure s
  putCache c = StateT $ \s -> (,) <$> putCache c <*> pure s
  
instance HasCache c m => HasCache c (ReaderT r m) where
  getCache = ReaderT $ const getCache
  putCache = ReaderT . const . putCache
  
instance HasCache c m => HasCache c (StepIndexT m) where
  getCache = StepIndexT $ getCache
  putCache = StepIndexT . putCache

(⊳) :: MonadFLAMIO m => FLAMIO a -> m a
(⊳) x = liftFLAMIO (FLAMIO (local (first (+ 1)) (unFLAMIO x)))

del :: (MonadFLAMIO m) => (Principal, Principal) -> m QueryResult
del (p, q) = do
  h <- getState
  strat <- getStrategy
  clr <- getClearance
  idx <- liftFLAMIO $ FLAMIO $ asks fst
  let run [] = return (False, Map.empty)
      run (stratClr : strat) =
        let f lab = do
              l <- liftLIO getLabel
              (b1, a1) <- (⊳) (labelOf lab ⊔ l .⊑. clr) >>= lowerB' idx
              (b2, a2) <- (⊳) (labelOf lab .⊑. stratClr) >>= lowerB' idx
              case (b1, b2) of
                (True, True) -> Just <$> ((,) <$> (⊳) (unlabel lab) <*> pure (a1 `Map.union` a2))
                _ -> return Nothing -- TODO: Should we record a1 and a2 here somehow?
        in setFilterMapM f (unH h) >>= reach (p, q) >>= \case
             (True, a) -> return (True, a)
             (False, a) -> second (Map.union a) <$> run strat
  uncurry (flip liftB) <$> run (unStrategy strat)

löb :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
löb (p, q) = do
  (idx, assumptions) <- liftFLAMIO $ FLAMIO ask
  let assumptions' = Map.takeWhileAntitone (<= idx) assumptions
  let x = Map.foldlWithKey' f Set.empty assumptions'
  uncurry (flip liftB) <$> reach (p, q) x
  where
    f x idx = Set.foldr' (\(p, q) -> Set.insert ((p, q), Map.singleton idx (Set.singleton (p, q)))) x

distrL :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
distrL ((:→) (p1 :/\ p2), q) = ((p1 →) /\ (p2 →)) .≽. q
distrL ((:→) (p1 :\/ p2), q) = ((p1 →) \/ (p2 →)) .≽. q
distrL ((:←) (p1 :/\ p2), q) = ((p1 ←) /\ (p2 ←)) .≽. q
distrL ((:←) (p1 :\/ p2), q) = ((p1 ←) \/ (p2 ←)) .≽. q
distrL _ = return $ Failed Map.empty

distrR :: MonadFLAMIO m => (Principal, Principal) -> m QueryResult
distrR (p, (:→) (q1 :/\ q2)) = p .≽. ((q1 →) /\ (q2 →))
distrR (p, (:→) (q1 :\/ q2)) = p .≽. ((q1 →) \/ (q2 →))
distrR (p, (:←) (q1 :/\ q2)) = p .≽. ((q1 ←) /\ (q2 ←))
distrR (p, (:←) (q1 :\/ q2)) = p .≽. ((q1 ←) \/ (q2 ←))
distrR _ = return $ Failed Map.empty

(.≽) :: MonadFLAMIO m => Principal -> Principal -> m QueryResult
p .≽ q =
  löb (p, q) <|||>
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
  conjL (p, q)

(≽) :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal) => a -> b -> m Bool
p ≽ q =
  runReaderT (unStepIndexT ((normalize (p %) .≽. normalize (q %)) >>= lowerB 0)) (0, Map.empty)

instance SemiLattice Principal where
  p .⊔. q = normalize (((p /\ q) →) /\ ((p \/ q) ←))
  p .⊓. q = normalize (((p \/ q) →) /\ ((p /\ q) ←))

instance Label H Principal where
  type C H Principal = MonadFLAMIO
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
reify (JNF c i) = ((:→) (reifyJ c)) :/\ ((:←) (reifyJ i))
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
  jNormInt p1 `jConj` jNormInt p2
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
infixr 7 /\

(\/) :: (ToLabel a Principal, ToLabel b Principal) => a -> b -> Principal
a \/ b = (a %) :\/ (b %)
infixr 7 \/

(→) :: (ToLabel a Principal) => a -> Principal
(→) a = (:→) (a %)

(←) :: (ToLabel a Principal) => a -> Principal
(←) a = (:←) (a %)

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
  
newtype FLAMIO a = FLAMIO { unFLAMIO :: StepIndexT (StateT Cache (LIO H FLAM)) a }
  deriving (Functor, Applicative, Monad)

instance MonadLIO H FLAM FLAMIO where
  liftLIO = FLAMIO . liftLIO

instance HasCache Cache FLAMIO where
  getCache = FLAMIO get
  putCache c = FLAMIO $ put c

(∇) :: (ToLabel a Principal) => a -> Principal
(∇) a = normalize $ (confidentiality p' ←) /\ (integrity p' ←)
  where p' = norm (a %)
  
addDelegate :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal, ToLabel c Principal) =>
               a -> b -> c -> m ()
addDelegate p q l = do
  lbl <- getLabel
  (,) <$> lbl ≽ (∇) q <*> (∇) (p →) ≽ (∇) (q →) >>= \case
    (True, True) -> do
      h <- liftLIO getState
      lab <- label l (normalize (p %), normalize (q %))
      liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
      liftLIO $ setState (H $ Set.insert lab (unH h))
    (False, _) -> error $ "IFC violation (addDelegate 1): " ++ show lbl ++ " ≽ " ++ show ((∇) q)
    (_, False) -> error $ "IFC violation (addDelegate 2): " ++ show ((∇) (p →)) ++ " ≽ " ++ show ((∇) (q →))

removeDelegate :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal, ToLabel c Principal) =>
                  a -> b -> c -> m ()
removeDelegate p q l = do
  h <- liftLIO getState
  lab <- label l (normalize (p %), normalize (q %))
  liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
  liftLIO $ setState (H $ Set.delete lab (unH h))

withStrategy :: (MonadFLAMIO m, ToLabel b Principal) => [b] -> m a -> m a
withStrategy newStrat m = do
  liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
  oldStrat <- liftLIO $ gets $ view _3
  liftLIO $ modify $ (_3 .~ Strategy (fmap (normalize . (%)) newStrat))
  x <- m
  liftLIO $ modify $ (_3 .~ oldStrat)
  return x

noStrategy :: Strategy Principal
noStrategy = Strategy []

newScope :: (MonadFLAMIO m) => m a -> m a
newScope m = do
  h <- liftLIO getState
  x <- m
  liftLIO $ setState h
  return x

{- Networking stuff -}
class Serializable a where
  encode :: a -> B.ByteString
  decode :: B.ByteString -> Maybe a
  maxSize :: a -> Int
  
data LSocket a where
  LSocket :: Serializable a => (Net.Socket, Principal) -> LSocket a
type IP = String
type Name = String
type Port = String
type Host a = (IP, Port, a)

channelLabel :: LSocket a -> Principal
channelLabel (LSocket (_, s)) = s
  
serve :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocket a -> m r) -> m ()
serve (ip, port, name) f = do
  Net.listen (Net.Host ip) port (\(socket, addr) -> Net.accept socket (\(socket', _) -> f (LSocket (socket', (%) name))))
  return ()
  
connect :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m, ToLabel b Principal) => Host b -> (LSocket a -> m r) -> m ()
connect (ip, port, name) f = do
  Net.connect ip port (\(socket, _) -> f (LSocket (socket, (%) name)))
  return ()

{- Q: Is it really bad to send to a principal above your clearance?
      If we did not have this, the battleship example could avoid adding the delegations
   A: If we don't do this we cannot get a theorem equivalent to the LIO's Theorem 3 (Containment imposed by clearance).
      But we don't really care about this one.... I think
-}
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

{- TODO: I would really like to have it return m (Labeled Principal (Maybe a)),
   but when we receive Nothing we don't know how to label it -}
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

instance MonadThrow m => MonadThrow (StepIndexT m) where
  throwM = StepIndexT . throwM
  
instance MonadCatch m => MonadCatch (StepIndexT m) where
  catch (StepIndexT m) f = StepIndexT $ catch m (unStepIndexT . f)
  
instance MonadMask m => MonadMask (StepIndexT m) where
  mask a = StepIndexT $ mask $ \u -> unStepIndexT (a $ q u)
    where q u (StepIndexT b) = StepIndexT (u b)

  uninterruptibleMask a = StepIndexT $ uninterruptibleMask $ \u -> unStepIndexT (a $ q u)
    where q u (StepIndexT b) = StepIndexT (u b)

  generalBracket acquire release use = StepIndexT $ generalBracket
    (unStepIndexT acquire)
    (\resource exitCase -> unStepIndexT (release resource exitCase))
    (\resource -> unStepIndexT (use resource))
  
instance MonadThrow FLAMIO where
  throwM = FLAMIO . throwM

instance MonadCatch FLAMIO where
  catch (FLAMIO m) f = FLAMIO $ catch m (unFLAMIO . f)

instance MonadMask FLAMIO where
  mask a = FLAMIO $ mask $ \u -> unFLAMIO (a $ q u)
    where q u (FLAMIO b) = FLAMIO (u b)

  uninterruptibleMask a = FLAMIO $ uninterruptibleMask $ \u -> unFLAMIO (a $ q u)
    where q u (FLAMIO b) = FLAMIO (u b)

  generalBracket acquire release use = FLAMIO $ generalBracket
    (unFLAMIO acquire)
    (\resource exitCase -> unFLAMIO (release resource exitCase))
    (\resource -> unFLAMIO (use resource))

{- Serialization instances for common types -}
instance Serializable Int where
  encode = BL.toStrict . Bin.encode
  decode x =
    case Bin.decodeOrFail (BL.fromStrict x) of
      Right (_, _, r) -> Just r
      _ -> Nothing
  maxSize _ = 8

instance Serializable Bool where
  encode = BL.toStrict . Bin.encode
  decode x = case Bin.decodeOrFail (BL.fromStrict x) of
      Right (_, _, r) -> Just r
      _ -> Nothing
  maxSize _ = 1

instance (Serializable a, Serializable b) => Serializable (a, b) where
  encode (a, b) = alen `B.append` a' `B.append` b'
    where a' = encode a
          b' = encode b
          alen = encode $ B.length a'

  decode bs =
    let (alen, rest) = B.splitAt (maxSize (undefined :: Int)) bs
    in case decode alen of
         Just (n :: Int) ->
           let (a, b) = B.splitAt n rest
           in case (decode a, decode b) of
                (Just a, Just b) -> Just (a, b)
                _ -> Nothing
         _ -> Nothing

  maxSize _ = maxSize (undefined :: Int) +
              maxSize (undefined :: a) +
              maxSize (undefined :: b)

instance (Serializable a, Serializable b, Serializable c) => Serializable (a, b, c) where
  encode (a, b, c) = alen `B.append` a' `B.append` encode (b, c)
    where a' = encode a
          alen = encode $ B.length a'
  decode bs =
    let (alen, rest) = B.splitAt (maxSize (undefined :: Int)) bs
    in case decode alen of
         Just (n :: Int) ->
           let (a, bc) = B.splitAt n rest
           in case (decode a, decode bc) of
                (Just a, Just (b, c)) -> Just (a, b, c)
                _ -> Nothing
         _ -> Nothing
          
  maxSize _ = maxSize (undefined :: Int) +
              maxSize (undefined :: a) +
              maxSize (undefined :: (b, c))

instance (Serializable a, Serializable b) => Serializable (Either a b) where
  encode (Left a) = B.cons 0 (encode a)
  encode (Right b) = B.cons 1 (encode b)

  decode bs =
    case B.uncons bs of
      Just (0, bs') -> Left <$> decode bs'
      Just (1, bs') -> Right <$> decode bs'
      _ -> Nothing

  maxSize _ = 1 + max (maxSize (undefined :: a)) (maxSize (undefined :: b))

instance Serializable String where
  encode = B8.pack
  decode = Just . B8.unpack
  maxSize _ = 1024

instance Serializable Principal where
  encode (:⊤) = B.singleton 0
  encode (:⊥) = B.singleton 1
  encode (Name s) = B.cons 2 (encode s)
  encode (p1 :/\ p2) = B.cons 3 (encode (p1, p2))
  encode (p1 :\/ p2) = B.cons 4 (encode (p1, p2))
  encode ((:→) p) = B.cons 5 (encode p)
  encode ((:←) p) = B.cons 6 (encode p)
  encode (p1 ::: p2) = B.cons 7 (encode (p1, p2))

  decode bs =
    case B.uncons bs of
      Just (0, _) -> Just (:⊤)
      Just (1, _) -> Just (:⊥)
      Just (2, bs') -> Name <$> decode bs'
      Just (3, bs') -> uncurry (:/\) <$> decode bs'
      Just (4, bs') -> uncurry (:\/) <$> decode bs'
      Just (5, bs') -> (:→) <$> decode bs'
      Just (6, bs') -> (:←) <$> decode bs'
      Just (7, bs') -> uncurry (:::) <$> decode bs'
      _ -> Nothing

  maxSize _ = 1024
  
instance Serializable a => Serializable (Labeled FLAM a) where
  encode (Labeled l a) = encode (l, a)
  decode bs = uncurry Labeled <$> decode bs
  maxSize _ = maxSize (undefined :: FLAM, undefined :: a)

runFLAM :: FLAMIO a -> LIO H FLAM a
runFLAM m = evalStateT (runReaderT (unStepIndexT $ unFLAMIO m) (0, Map.empty)) emptyCache

instance MonadFLAMIO FLAMIO where
  liftFLAMIO = id

instance MonadFLAMIO m => MonadFLAMIO (StateT s m) where
 liftFLAMIO = lift . liftFLAMIO

instance MonadFLAMIO m => MonadFLAMIO (ReaderT r m) where
  liftFLAMIO = lift . liftFLAMIO

instance MonadFLAMIO m => MonadFLAMIO (StepIndexT m) where
  liftFLAMIO = lift . liftFLAMIO

instance MonadIO m => MonadIO (StepIndexT m) where
  liftIO = StepIndexT . liftIO

{- NOTE: This is a dangerous operation that should be put in a seperate (TCB) module! -}
instance MonadIO FLAMIO where
  liftIO = FLAMIO . liftIO
