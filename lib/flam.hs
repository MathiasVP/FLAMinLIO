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

import Data.POMap.Internal(mkPOMap, POMap(..))

import Data.Proxy

{- For networking -}
import Control.Monad.Catch
import qualified Data.Binary as Bin
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Char8 as B8
import qualified Network.Simple.TCP as Net

{- TODO: Hopefully this will be put into the POMaps module at some point -}
takeWhileAntitone :: (k -> Bool) -> POMap k a -> POMap k a
takeWhileAntitone p (POMap _ d) = mkPOMap (Map.takeWhileAntitone p <$> d)

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
    if n > 10 then showString "(" . showsPrec 11 p . showString " ←" . showString ")"
    else showsPrec 11 p . showString " ←"
  showsPrec n ((:←) p) =
    if n > 10 then showString "(" . showsPrec 11 p . showString " →" . showString ")"
    else showsPrec 11 p . showString " →"
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

data ProgressCondition l
  = ActsFor !l !l
  | Conj !(ProgressCondition l) !(ProgressCondition l)
  | Disj !(ProgressCondition l) !(ProgressCondition l)
  | TrueCondition
  | FalseCondition
  deriving Eq

instance Show l => Show (ProgressCondition l) where
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

type Assumptions = Map Int (Principal, Principal)
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

type SureCache l = Map (l, l) (Map Int (Map (l, l) l))
type UnsureCache l = Map Int (Map (l, l) (ProgressCondition l))

type ReachabilityCache l = Map (Set (l, l)) ((Set (J, J), Set (J, J)))
type ProvedCache l = POMap (Assumptions, Strategy l, H) (SureCache l)
-- NOTE: The fact that PrunedCache is a map from assumptions to pruned results means
-- that we have a lot of pruned cache misses.
-- This is without a doubt the main source of slowdown currently. But we cannot have it in a partial ordered map
-- with either subset of superset inclusion since we don't know if the result ends up being proved or failed. Hmmm....
type PrunedCache l = Map Assumptions (Map (l, l) (UnsureCache l))
type FailedCache l = POMap (Op (Assumptions, Strategy l, H)) (SureCache l)
data Cache l = Cache { _reachabilityCache :: !(ReachabilityCache l),
                     _provedCache :: !(ProvedCache l),
                     _prunedCache :: !(PrunedCache l),
                     _failedCache :: !(FailedCache l) }
makeLenses ''Cache

emptyCache :: Cache Principal
emptyCache = Cache { _reachabilityCache = Map.empty,
                     _provedCache = POMap.empty,
                     _prunedCache = Map.empty,
                     _failedCache = POMap.empty }

newtype Original t = Original t
newtype Replacement t = Replacement t
newtype Pattern t = Pattern t

-- substitute oldpc newpc pc means pc[oldpc -> newpc]
substitute :: Eq l => Pattern (ProgressCondition l) -> Replacement (ProgressCondition l) -> Original (ProgressCondition l) -> ProgressCondition l
substitute (Pattern oldpc) (Replacement newpc) (Original pc) | oldpc == pc = newpc
substitute oldpc newpc (Original (Conj pc1 pc2)) =
  Conj (substitute oldpc newpc (Original pc1)) (substitute oldpc newpc (Original pc2))
substitute oldpc newpc (Original (Disj pc1 pc2)) =
  Disj (substitute oldpc newpc (Original pc1)) (substitute oldpc newpc (Original pc2))
substitute _ _ (Original pc) = pc

data QueryResult l
  = Failed
  | Success
  | Pruned !(ProgressCondition l)
  deriving Show

liftB :: Bool -> QueryResult l
liftB True = Success
liftB False = Failed

lowerB :: MonadFLAMIO m => Int -> QueryResult Principal -> m Bool
lowerB idx Success = return True
lowerB idx Failed = return False
lowerB idx (Pruned pc) =
  isTrue idx pc >>= \case
    Just b -> return b
    Nothing -> return False
  
setFilterMapM :: (Ord a, Ord b, Monad m) => (a -> m (Maybe b)) -> Set a -> m (Set b)
setFilterMapM f s = visit s Set.empty
  where visit (setview -> Nothing) s = return s
        visit (setview -> Just (a, as)) s =
          f a >>= \case
            Nothing -> visit as s
            Just b -> visit as (Set.insert b s)

(<&&&>) :: (Monad m) => m (QueryResult l) -> m (QueryResult l) -> m (QueryResult l)
(<&&&>) m1 m2 =
  m1 >>= \case
    Success -> m2
    Failed -> return Failed
    Pruned pc1 ->
      m2 >>= \case
        Success -> return $ Pruned pc1
        Failed -> return Failed
        Pruned pc2 -> return $ Pruned $ pc1 `Conj` pc2
infixr 8 <&&&>

(<|||>) :: (Monad m) => m (QueryResult l) -> m (QueryResult l) -> m (QueryResult l)
(<|||>) m1 m2 =
  m1 >>= \case
    Success -> return Success
    Failed -> m2
    Pruned pc1 ->
      m2 >>= \case
        Success -> return Success
        Failed -> return $ Pruned pc1
        Pruned pc2 -> return $ Pruned $ pc1 `Disj` pc2
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

isTrue :: MonadFLAMIO m => Int -> ProgressCondition Principal -> m (Maybe Bool)
isTrue idx (ActsFor p q) = do
  (_, assumptions) <- liftFLAMIO $ FLAMIO $ ask
  let assumptions' = Map.takeWhileAntitone (<= idx) assumptions
  b <- reach (p, q) (Set.fromAscList . Map.elems $ assumptions')
  case b of
    True -> return $ Just True
    False -> return Nothing
isTrue idx (Conj pc1 pc2) =
  isTrue idx pc1 >>= \case
    Just True -> isTrue idx pc2
    Just False -> return $ Just False
    Nothing -> return $ Nothing
isTrue idx (Disj pc1 pc2) =
 isTrue idx pc1 >>= \case
   Just True -> return $ Just True
   Just False -> isTrue idx pc1
   Nothing -> return $ Nothing
isTrue _ TrueCondition = return $ Just True
isTrue _ FalseCondition = return $ Just False

isFalse :: MonadFLAMIO m => Int -> ProgressCondition Principal -> m (Maybe Bool)
isFalse idx pc =
  isTrue idx pc >>= \case
    Just b -> return $ Just $ not b
    Nothing -> return $ Nothing

mapMaybeKeepM :: (Ord k, Monad m) => (a -> m (Maybe b)) -> Map k a -> m (Map k a, Map k b)
mapMaybeKeepM _ (mapview -> Nothing) = return (Map.empty, Map.empty)
mapMaybeKeepM f (mapview -> Just ((k, a), m)) = do
  (m1, m2) <- mapMaybeKeepM f m
  f a >>= \case
    Just b -> return (m1, Map.insert k b m2)
    Nothing -> return (Map.insert k a m1, m2)

alterSure :: Ord l => (Maybe (Map Int (Map (l, l) l)) -> Maybe (Map Int (Map (l, l) l))) ->
             l -> l ->
             Maybe (SureCache l) -> Maybe (SureCache l)
alterSure f cur clr Nothing = Map.singleton (cur, clr) <$> f Nothing
alterSure f cur clr (Just m) = Map.insert (cur, clr) <$> f (Map.lookup (cur, clr) m) <*> pure m

insert p q idx cur Nothing = Map.singleton idx (Map.singleton (p, q) cur)
insert p q idx cur (Just map) =
  case Map.lookup idx map of
    Just m -> Map.insert idx (Map.insert (p, q) cur m) map
    Nothing -> Map.insert idx (Map.singleton (p, q) cur) map

updatePruned :: (Eq l, Monad m) => Int -> l -> l -> ProgressCondition l ->
                (Int -> ProgressCondition l -> m (Maybe Bool)) -> ProgressCondition l ->
                m (Maybe (ProgressCondition l))
updatePruned idx p q rep cond progCond = do
          let progCond' = substitute (Pattern (ActsFor p q)) (Replacement rep) (Original progCond)
          cond idx progCond' >>= \case
            Just True -> do
              return Nothing
            Just False -> do
              return $ Just progCond'
            Nothing -> do
              return $ Just progCond'

update :: forall m . MonadFLAMIO m => (Principal, Principal) -> Int -> (Principal, Principal) -> QueryResult Principal -> m ()
update (cur, clr) idx (p, q) Success = do
  cur' <- liftLIO getLabel
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  assumptions <- liftFLAMIO $ FLAMIO $ asks snd
  liftFLAMIO $ modifyCache $ over provedCache $ POMap.alter (alterSure (Just . insert p q idx cur') cur clr) (assumptions, strat, h)
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.update (Just . Map.update (Just . Map.mapWithKey delete) (cur, clr)) assumptions
  prunedmap <- Map.lookup assumptions <$> liftFLAMIO (getsCache (view prunedCache)) >>= \case
    Just prunedmap ->
      case Map.lookup (cur, clr) prunedmap of
        Just pm -> mapMapWithKeyM (\idx' -> if idx <= idx' then mapMapMaybeM (updatePruned idx p q TrueCondition isTrue)
                                            else return) pm
        Nothing -> return Map.empty
    Nothing -> return Map.empty
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.alter (Just . \case
                                                              Just m -> Map.insert (cur, clr) prunedmap m
                                                              Nothing -> Map.singleton (cur, clr) prunedmap
                                                          ) assumptions
  where delete idx' m = if idx <= idx' then Map.delete (cur, clr) m else m
  
update (cur, clr) idx (p, q) (Pruned pc) = do
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  assumptions <- liftFLAMIO $ FLAMIO $ asks snd
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.update (Just . Map.alter (Just . insert p q idx pc) (cur, clr)) assumptions
  prunedmap <- Map.lookup assumptions <$> liftFLAMIO (getsCache (view prunedCache)) >>= \case
    Just prunedmap ->
      case Map.lookup (cur, clr) prunedmap of
        Just pm -> return $ Map.mapWithKey (\idx' -> if idx <= idx' then Map.map (updatePruned idx) else id) pm
        Nothing -> return Map.empty
    Nothing -> return Map.empty
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.alter (Just . \case
                                                            Just m -> Map.insert (cur, clr) prunedmap m
                                                            Nothing -> Map.singleton (cur, clr) prunedmap
                                                        ) assumptions
  where updatePruned :: Int -> ProgressCondition Principal -> ProgressCondition Principal
        updatePruned idx = substitute (Pattern (ActsFor p q)) (Replacement pc) . Original
        
update (cur, clr) idx (p, q) Failed = do
  cur' <- liftLIO getLabel
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  assumptions <- liftFLAMIO $ FLAMIO $ asks snd
  liftFLAMIO $ modifyCache $ over failedCache $ POMap.alter
    (alterSure (Just . insert p q idx cur') cur clr) (Op (assumptions, strat, h))
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.update (Just . Map.update (Just . Map.mapWithKey delete) (cur, clr)) assumptions

  (new, prunedmap) <- Map.lookup assumptions <$> liftFLAMIO (getsCache (view prunedCache)) >>= \case
    Just prunedmap ->
      case Map.lookup (cur, clr) prunedmap of
        Just prunedmap ->
          foldrM (\(idx', m) (new, pruned) -> do
                     (new', pruned') <- mapMaybeKeepM (updatePruned idx p q FalseCondition isFalse) m
                     return ((idx', new') : new, (idx', pruned') : pruned)
                 ) ([], []) (Map.toList prunedmap')
          where prunedmap' = Map.filterWithKey (\idx' -> if idx <= idx' then const True else const False) prunedmap
        Nothing -> return ([], [])
    Nothing -> return ([], [])
  liftFLAMIO $ modifyCache $ over prunedCache $ Map.insert assumptions ((Map.insert (cur, clr) (List.foldr (uncurry Map.insert) Map.empty prunedmap)) Map.empty)
  forM_ new $ \(idx', m) -> mapM_ (\(p, q) -> update (cur, clr) idx' (p, q) Failed) (Map.keys m)
     where delete idx' m = if idx <= idx' then Map.delete (cur, clr) m else m

searchSureCache :: (Principal, Principal) -> Int ->
                   Map Int (Map (Principal, Principal) Principal) -> Maybe Principal
searchSureCache (p, q) idx m =
  let m' = Map.takeWhileAntitone (<= idx) m
  in Map.lookup (p, q) (Map.unions $ Map.elems m')

searchSurePOMap (cur, clr) (p, q) idx m = search (POMap.elems m)
  where search :: [SureCache Principal] -> Maybe Principal
        search [] = Nothing
        search (c : cs) =
          case Map.lookup (cur, clr) c of
          Just m -> case searchSureCache (p, q) idx m of
                      Just p -> Just p
                      Nothing -> search cs
          Nothing -> search cs

searchFailedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe Principal)
searchFailedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO getCache
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  (idx, assumptions) <- liftFLAMIO $ FLAMIO ask
  let failedcache = takeWhileAntitone (`leq` Op (assumptions, strat, h)) (view failedCache cache)
  return $ searchSurePOMap (cur, clr) (p, q) idx failedcache
  
searchProvedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe Principal)
searchProvedCache (cur, clr) (p, q) = do
  cache <- liftFLAMIO $ getCache
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  (idx, assumptions) <- liftFLAMIO $ FLAMIO ask
  let provedcache = takeWhileAntitone (`leq` (assumptions, strat, h)) (view provedCache cache)
  return $ searchSurePOMap (cur, clr) (p, q) idx provedcache
  
data CacheSearchResult l
  = ProvedResult !l
  | FailedResult !l
  | PrunedResult !(ProgressCondition l)

searchPrunedCache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (ProgressCondition Principal))
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
          in return $ Map.lookup (p, q) uc'
        Nothing -> return Nothing
    Nothing -> return Nothing
    
searchcache :: MonadFLAMIO m => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (CacheSearchResult Principal))
searchcache (cur, clr) (p, q) = do
  let failedSearch = searchFailedCache (cur, clr) (p, q)
      prunedSearch = searchPrunedCache (cur, clr) (p, q)
      provedSearch = searchProvedCache (cur, clr) (p, q)
  (,,) <$> provedSearch <*> failedSearch <*> prunedSearch >>= \case
    (Just cur', _, _) -> return $ Just $ ProvedResult cur'
    (_, Just cur', _) -> return $ Just $ FailedResult cur'
    (_, _, Just pc) -> return $ Just $ PrunedResult pc
    (_, _, _) -> return Nothing

instance MonadLIO s l m => MonadLIO s l (StepIndexT m) where
  liftLIO = lift . liftLIO
  
instance MonadTrans StepIndexT where
  lift = StepIndexT . lift 

withLöb :: MonadFLAMIO m => (Principal, Principal) -> FLAMIO a -> m a
withLöb (p, q) m = do
  (idx, _) <- liftFLAMIO $ FLAMIO ask
  liftFLAMIO $ FLAMIO $ local (second $ Map.insert (idx + 1) (normalize p, normalize q)) (unFLAMIO m)

(.≽.) :: MonadFLAMIO m => Principal -> Principal -> m (QueryResult Principal)
p .≽. q = do
  curLab <- liftLIO getLabel
  clrLab <- liftLIO getClearance
  (idx, _) <- liftFLAMIO $ FLAMIO ask
  x <- searchcache (curLab, clrLab) (p, q)
  case x of
    Just (ProvedResult cur') -> do
      liftLIO $ modify $ (_1 . cur) .~ cur'
      return Success
    Just (FailedResult cur') -> do
      liftLIO $ modify $ (_1 . cur) .~ cur'
      return Failed
    Just (PrunedResult pc) -> do
      return $ Pruned pc
    Nothing -> do
      update (curLab, clrLab) idx (p, q) (Pruned (ActsFor p q))
      r <- withLöb (p, q) (p .≽ q)
      update (curLab, clrLab) idx (p, q) r
      return r

bot_ :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
bot_ (_, (:⊥)) = return Success
bot_ (_, (((:→) (:⊥)) :/\ ((:←) (:⊥)))) = return Success
bot_ _ = return Failed

top_ :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
top_ ((:⊤), _) = return Success
top_ ((((:→) (:⊤)) :/\ ((:←) (:⊤))), _) = return Success
top_ _ = return Failed

refl :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
refl (p, q) | p == q = return Success
refl _ = return Failed

proj :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
proj ((:→) p, (:→) q) = p .≽. q
proj ((:←) p, (:←) q) = p .≽. q
proj _ = return Failed

projR :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
projR (p, (:←) q) | p == q = return Success
projR (p, (:→) q) | p == q = return Success
projR _ = return Failed

own1 :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
own1 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. p'
own1 _ = return Failed

own2 :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
own2 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. (o' ::: p')
own2 _ = return Failed

conjL :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
conjL (p1 :/\ p2, p) = p1 .≽. p <|||> p2 .≽. p
conjL _ = return Failed

conjR :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
conjR (p, p1 :/\ p2) = p .≽. p1 <&&&> p .≽. p2
conjR _ = return Failed

disjL :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
disjL (p1 :\/ p2, p) = p1 .≽. p <&&&> p2 .≽. p
disjL _ = return Failed

disjR :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
disjR (p, p1 :\/ p2) = p .≽. p1 <|||> p .≽. p2
disjR _ = return Failed

reach :: MonadFLAMIO m => (Principal, Principal) -> Set (Principal, Principal) -> m Bool
reach (p, q) s = do
  let pNorm = norm p
      qNorm = norm q

  cache <- liftFLAMIO $ getsCache $ view reachabilityCache
  (sconf, sint) <- 
    case Map.lookup s cache of
      Just (sconf, sint) -> return (sconf, sint)
      Nothing -> do
        let sconf, sint :: Set (J, J)
            (sconf, sint) = (transitive *** transitive) .
                          (atomize *** atomize) . expand $ s
        liftFLAMIO $ modifyCache $ over reachabilityCache (Map.insert s (sconf, sint))
        return (sconf, sint)
  return $
    (confidentiality pNorm, confidentiality qNorm) `Set.member` sconf &&
    (integrity pNorm, integrity qNorm) `Set.member` sint
        
{- Compute the expanded form of a delegation set -}
expand :: Set (Principal, Principal) -> (Set (J, M), Set (J, M))
expand s = (expand' sconf, expand' sint)
  where
    s' = Set.map (norm *** norm) s 
    sconf :: Set (J, J)
    sconf = Set.map (confidentiality *** confidentiality) s'
    sint :: Set (J, J)
    sint = Set.map (integrity *** integrity) s'

    expand' :: Set (J, J) -> Set (J, M)
    expand' = Set.foldr' (\(p, J q) ->
                            Set.union (Set.fromList [(p', q')
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
atomize :: Set (J, M) -> Set (J, J)
atomize s = Set.fromList
            [(J p', J (Set.singleton (M q'))) |
              (J p, M q) <- Set.toList s, p' <- Set.toList (powerset p), q' <- Set.toList (powerset q)]

{- Compute transitive closure of a set -}
transitive :: (Ord a, Eq a) => Set (a, a) -> Set (a, a)
transitive s
  | s == s' = s
  | otherwise = transitive s'
  where s' = s `Set.union` Set.fromList [(a, c) | (a, b) <- Set.toList s, (b', c) <- Set.toList s, b == b']

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
(⊳) x = liftFLAMIO (FLAMIO (local (first $ (+ 1)) (unFLAMIO x)))

del :: (MonadFLAMIO m) => (Principal, Principal) -> m (QueryResult Principal)
del (p, q) = do
  h <- getState
  strat <- getStrategy
  clr <- getClearance
  idx <- liftFLAMIO $ FLAMIO $ asks fst
  r <- anyM (\stratClr ->
               let f lab = do
                     l <- liftLIO getLabel
                     b1 <- (⊳) (labelOf lab ⊔ l .⊑. clr) >>= lowerB idx
                     b2 <- (⊳) (labelOf lab .⊑. stratClr) >>= lowerB idx
                     case (b1, b2) of
                       (True, True) -> Just <$> (⊳) (unlabel lab)
                       _ -> return Nothing
               in setFilterMapM f (unH h) >>= reach (p, q)) (unStrategy strat)
  return $ liftB r

löb :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
löb (p, q) = do
  (idx, assumptions) <- liftFLAMIO $ FLAMIO ask
  let assumptions' = Map.takeWhileAntitone (<= idx) assumptions
  liftB <$> reach (p, q) (Set.fromAscList . Map.elems $ assumptions')

distrL :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
distrL ((:→) (p1 :/\ p2), q) = ((p1 →) /\ (p2 →)) .≽. q
distrL ((:→) (p1 :\/ p2), q) = ((p1 →) \/ (p2 →)) .≽. q
distrL ((:←) (p1 :/\ p2), q) = ((p1 ←) /\ (p2 ←)) .≽. q
distrL ((:←) (p1 :\/ p2), q) = ((p1 ←) \/ (p2 ←)) .≽. q
distrL _ = return Failed

distrR :: MonadFLAMIO m => (Principal, Principal) -> m (QueryResult Principal)
distrR (p, (:→) (q1 :/\ q2)) = p .≽. ((q1 →) /\ (q2 →))
distrR (p, (:→) (q1 :\/ q2)) = p .≽. ((q1 →) \/ (q2 →))
distrR (p, (:←) (q1 :/\ q2)) = p .≽. ((q1 ←) /\ (q2 ←))
distrR (p, (:←) (q1 :\/ q2)) = p .≽. ((q1 ←) \/ (q2 ←))
distrR _ = return Failed
 
(.≽) :: MonadFLAMIO m => Principal -> Principal -> m (QueryResult Principal)
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
  p ⊔ q = normalize (((p /\ q) →) /\ ((p \/ q) ←))
  p ⊓ q = normalize (((p \/ q) →) /\ ((p /\ q) ←))

instance Label H Principal where
  type C H Principal = MonadFLAMIO
  p ⊑ q = ((q →) /\ (p ←)) ≽ ((p →) /\ (q ←))

(.⊑.) :: MonadFLAMIO m => Principal -> Principal -> m (QueryResult Principal)
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

bot :: Principal
bot = (:→) (:⊥) :/\ (:←) (:⊤)

top :: Principal
top = (:→) (:⊤) :/\ (:←) (:⊥)
  
newtype FLAMIO a = FLAMIO { unFLAMIO :: StepIndexT (StateT (Cache Principal) (LIO H FLAM)) a }
  deriving (Functor, Applicative, Monad)

instance MonadLIO H FLAM FLAMIO where
  liftLIO = FLAMIO . liftLIO

instance HasCache (Cache Principal) FLAMIO where
  getCache = FLAMIO get
  putCache c = FLAMIO $ put c
  
addDelegate :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal, ToLabel c Principal) =>
               (a, b) -> c -> m ()
addDelegate (p, q) l = do
  h <- liftLIO getState
  lab <- label l (normalize (p %), normalize (q %))
  liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
  liftLIO $ setState (H $ Set.insert lab (unH h))

removeDelegate :: (MonadFLAMIO m, ToLabel a Principal, ToLabel b Principal, ToLabel c Principal) =>
                  (a, b) -> c -> m ()
removeDelegate (p, q) l = do
  h <- liftLIO getState
  lab <- label l (normalize (p %), normalize (q %))
  liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
  liftLIO $ setState (H $ Set.delete lab (unH h))

withStrategy :: (MonadFLAMIO m, ToLabel b Principal) => Strategy b -> m a -> m a
withStrategy newStrat m = do
  liftFLAMIO $ modifyCache $ prunedCache .~ Map.empty
  oldStrat <- liftLIO $ gets $ view _3
  liftLIO $ modify $ (_3 .~ fmap (normalize . (%)) newStrat)
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
  LSocket :: Serializable a => (Net.Socket, String) -> LSocket a
type IP = String
type Name = String
type Port = String
type Host = (IP, Port, Name)

channelLabel :: LSocket a -> String
channelLabel (LSocket (_, s)) = s
  
serve :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m) => Host -> (LSocket a -> m r) -> m (Labeled Principal r)
serve (ip, port, name) f = do
  x <- Net.listen (Net.Host ip) port (\(socket, addr) -> Net.accept socket (\(socket', _) -> f (LSocket (socket', name))))
  label name x
  
connect :: (MonadIO m, Serializable a, MonadMask m, MonadFLAMIO m) => Host -> (LSocket a -> m r)
        -> m (Labeled Principal r)
connect (ip, port, name) f = do
  x <- Net.connect ip port (\(socket, _) -> f (LSocket (socket, name)))
  label name x

{- Q: Is it really bad to send to a principal above your clearance?
      If we did not have this, the battleship example could avoid adding the delegations
   A: If we don't do this we cannot get a theorem equivalent to the LIO's Theorem 3 (Containment imposed by clearance)
-}
send :: (MonadIO m, MonadMask m, MonadFLAMIO m, ToLabel c Principal) => LSocket a -> c -> a -> m ()
send (LSocket (s, name)) me a = do
  lab <- liftLIO $ gets $ view _1
  b <- (name %) ∈ lab
  unless b $
    fail ("IFC violation (send): " ++
           show (view cur lab) ++
           " ⊑ " ++ show (Name name) ++
           " ⊑ " ++ show (view clearance lab))
  d <- label me a
  Net.send s (encode d)

{- I would really like to have it return m (Labeled Principal (Maybe a)),
   but when we receive Nothing we don't know how to label it -}
recv :: forall m a . (MonadIO m, MonadMask m, MonadFLAMIO m) => LSocket a -> m (Maybe (Labeled Principal a))
recv (LSocket (s, name)) =
  Net.recv s (maxSize (undefined :: Labeled Principal a)) >>= \case
    Nothing -> return Nothing
    Just x -> do
      case decode x of
        Nothing -> return Nothing
        Just y -> return $ Just y

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
