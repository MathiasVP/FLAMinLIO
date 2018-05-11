{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, ViewPatterns, PostfixOperators, MultiParamTypeClasses, ExplicitForAll, ScopedTypeVariables, LambdaCase, MonadComprehensions, GeneralizedNewtypeDeriving, UndecidableInstances, DeriveGeneric #-}
module FLAM where

import LIO
import TCB()
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.POMap.Strict as POMap
import Data.POMap.Strict(POMap)
import qualified Data.Set as Set
import Data.Set(Set, (\\))
import Data.Either
import Data.String
import Control.Monad.State
import Control.Applicative
import qualified Data.Maybe as Maybe
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Arrow
import Control.Lens.Tuple
import Control.Lens
import Algebra.PartialOrd
import Control.Monad.Extra

-- Debugging!
import Control.Exception
import System.IO
import Data.IORef
import System.IO.Unsafe

listview :: Ord a => Set a -> [a]
listview = Set.toList

setview :: Ord a => Set a -> Maybe (a, Set a)
setview = Set.minView

mapview :: Map k a -> Maybe ((k, a), Map k a)
mapview = Map.minViewWithKey

counter :: IORef Int
{-# NOINLINE counter #-}
counter = unsafePerformIO (newIORef 0)

data Principal
  = (:⊤)
  | (:⊥)
  | Name String
  | Principal :/\ Principal
  | Principal :\/ Principal
  | (:→) Principal
  | (:←) Principal
  | Principal ::: Principal
  deriving (Eq, Ord, Show)

newtype H = H { unH :: Set (Labeled Principal (Principal, Principal)) }
  deriving (Ord, Eq, Show)

data L
  = N String
  | T
  | B
  | L :.: L
  deriving (Eq, Ord, Show)

newtype M = M { unM :: Set L } -- L₁ \/ L₂ \/ ... \/ Lₙ
  deriving (Eq, Ord, Show)

newtype J = J { unJ :: Set M } -- M₁ /\ M₂ /\ ... /\ Mₙ
  deriving (Eq, Ord, Show)

data JNF = JNF { confidentiality :: J, integrity :: J }
  deriving (Show, Eq, Ord)

data ProgressCondition l
  = ActsFor l l
  | Conj (ProgressCondition l) (ProgressCondition l)
  | Disj (ProgressCondition l) (ProgressCondition l)
  | TrueCondition
  | FalseCondition
  deriving (Show, Eq)

type ReachabilityCache l = Map (Set (l, l)) ((Set (J, J), Set (J, J)))
type ProvedCache l = Map (l, l, H, Strategy l) (Map (l, l) l)
type PrunedCache l = Map (l, l) (Map (l, l) (ProgressCondition l))
type FailedCache l = Map (l, l, H, Strategy l) (Map (l, l) l)
data Cache l = Cache { _reachabilityCache :: ReachabilityCache l,
                     _provedCache :: ProvedCache l,
                     _prunedCache :: PrunedCache l,
                     _failedCache :: FailedCache l }

makeLenses ''Cache

emptyCache :: Cache Principal
emptyCache = Cache { _reachabilityCache = Map.empty,
                     _provedCache = Map.empty,
                     _prunedCache = Map.empty,
                     _failedCache = Map.empty }

newtype Original t = Original t
newtype Replacement t = Replacement t
newtype Pattern t = Pattern t

-- substitute oldpc newpc pc means pc[oldpc -> newpc]
substitute :: Eq l => Pattern (ProgressCondition l) -> Replacement (ProgressCondition l) ->
              Original (ProgressCondition l) -> ProgressCondition l
substitute (Pattern oldpc) (Replacement newpc) (Original pc) | oldpc == pc = newpc
substitute oldpc newpc (Original (Conj pc1 pc2)) =
  Conj (substitute oldpc newpc (Original pc1)) (substitute oldpc newpc (Original pc2))
substitute oldpc newpc (Original (Disj pc1 pc2)) =
  Disj (substitute oldpc newpc (Original pc1)) (substitute oldpc newpc (Original pc2))
substitute _ _ (Original progCond) = progCond

data QueryResult l
  = Failed
  | Success
  | Pruned (ProgressCondition l)
  deriving Show

liftB :: Bool -> QueryResult l
liftB True = Success
liftB False = Failed

lowerB :: QueryResult Principal -> Bool
lowerB Success = True
lowerB Failed = False
lowerB (Pruned pc) = isSatisfied pc

setFilterMapM :: (Ord a, Ord b, Monad m) => (a -> m (Maybe b)) -> Set a -> m (Set b)
setFilterMapM f s = visit s Set.empty
  where visit (setview -> Nothing) s = return s
        visit (setview -> Just (a, as)) s =
          f a >>= \case
            Nothing -> visit as s
            Just b -> visit as (Set.insert b s)

mapFilterM :: (Ord k, Monad m) => (a -> m Bool) -> Map k a -> m (Map k a)
mapFilterM p m = visit m Map.empty
  where visit (mapview -> Nothing) m = return m
        visit (mapview -> Just ((k, a), m')) m =
          p a >>= \case
            False -> visit m' m
            True -> visit m' (Map.insert k a m)

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

isSatisfied :: ProgressCondition Principal -> Bool
isSatisfied (ActsFor p q) = False
isSatisfied (Conj pc1 pc2) =
  case isSatisfied pc1 of
    True -> isSatisfied pc2
    False -> False
isSatisfied (Disj pc1 pc2) =
 case isSatisfied pc1 of
   True -> True
   False -> isSatisfied pc1
isSatisfied TrueCondition = True
isSatisfied FalseCondition = False

isFalse :: ProgressCondition Principal -> Bool
isFalse = not . isSatisfied

mapMaybeKeepM :: (Ord k, Monad m) => (a -> m (Maybe b)) -> Map k a -> m (Map k a, Map k b)
mapMaybeKeepM _ (mapview -> Nothing) = return (Map.empty, Map.empty)
mapMaybeKeepM f (mapview -> Just ((k, a), m)) = do
  (m1, m2) <- mapMaybeKeepM f m
  f a >>= \case
    Just b -> return (m1, Map.insert k b m2)
    Nothing -> return (Map.insert k a m1, m2)

instance HasCache c m => HasCache c (ReaderT r m) where
  getCache = lift getCache
  putCache = lift . putCache
  
update :: forall m . (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> (Principal, Principal) -> QueryResult Principal -> m ()
update (cur, clr) (p, q) Success = do
  cur' <- liftLIO getLabel
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  modifyCache $ over provedCache $ Map.alter (insertProved cur') (cur, clr, h, strat)
  modifyCache $ over prunedCache $ Map.update (Just . Map.delete (p, q)) (cur, clr)
  prunedmap <- Map.lookup (cur, clr) <$> getsCache (view prunedCache) >>= \case
    Just prunedmap -> mapMapMaybeM updatePruned prunedmap
    Nothing -> return Map.empty
  
  modifyCache $ over prunedCache $ Map.insert (cur, clr) prunedmap
  where insertProved cur Nothing = Just $ Map.singleton (p, q) cur
        insertProved cur (Just map) = Just $ Map.insert (p, q) cur map

        updatePruned :: ProgressCondition Principal -> m (Maybe (ProgressCondition Principal))
        updatePruned progCond = do
          let progCond' = substitute (Pattern (ActsFor p q)) (Replacement TrueCondition) (Original progCond)
          case isSatisfied progCond' of
            True -> return Nothing
            False -> return $ Just progCond'
update (cur, clr) (p, q) (Pruned progCond) = do
  modifyCache $ over prunedCache $ Map.alter insertPruned (cur, clr)
  prunedmap <- Map.lookup (cur, clr) <$> getsCache (view prunedCache) >>= \case
    Just prunedmap -> return $ Map.map updatePruned prunedmap
    Nothing -> return Map.empty
  modifyCache $ over prunedCache $ Map.insert (cur, clr) prunedmap
  where insertPruned Nothing = Just $ Map.singleton (p, q) progCond
        insertPruned (Just map) = Just $ Map.insert (p, q) progCond map

        updatePruned :: ProgressCondition Principal -> ProgressCondition Principal
        updatePruned = substitute (Pattern (ActsFor p q)) (Replacement progCond) . Original
update (cur, clr) (p, q) Failed = do
  cur' <- liftLIO getLabel
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  modifyCache $ over failedCache $ Map.alter (insertFailed cur') (cur, clr, h, strat)
  modifyCache $ over prunedCache $ Map.update (Just . Map.delete (p, q)) (cur, clr)
  (new, prunedmap) <- Map.lookup (cur, clr) <$> getsCache (view prunedCache) >>= \case
    Just prunedmap -> mapMaybeKeepM updatePruned prunedmap
    Nothing -> return (Map.empty, Map.empty)
  modifyCache $ over prunedCache $ Map.insert (cur, clr) prunedmap
  forM_ (Map.keys new) $ flip (update (cur, clr)) Failed
  where insertFailed cur Nothing = Just $ Map.singleton (p, q) cur
        insertFailed cur (Just map) = Just $ Map.insert (p, q) cur map
        
        updatePruned :: ProgressCondition Principal -> m (Maybe (ProgressCondition Principal))
        updatePruned progCond = do
          let progCond' = substitute (Pattern (ActsFor p q)) (Replacement FalseCondition) (Original progCond)
          case isFalse progCond' of
            True -> return Nothing
            False -> return $ Just progCond'

searchFailedCache :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> (Principal, Principal) -> m (Maybe Principal)
searchFailedCache (cur, clr) (p, q) = do
  cache <- getCache
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  case Map.lookup (cur, clr, h, strat) (view failedCache cache) of
    Just failed ->
      case Map.lookup (p, q) failed of
        Just cur' -> return $ Just cur'
        Nothing -> return Nothing
    Nothing -> return Nothing

searchProvedCache :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> (Principal, Principal) -> m (Maybe Principal)
searchProvedCache (cur, clr) (p, q) = do
  cache <- getCache
  h <- liftLIO $ gets $ view _2
  strat <- liftLIO $ gets $ view _3
  case Map.lookup (cur, clr, h, strat) (view provedCache cache) of
    Just pcache ->
      case Map.lookup (p, q) pcache of
        Just cur' -> return $ Just cur'
        Nothing -> return Nothing
    Nothing -> return Nothing

data CacheSearchResult l
  = ProvedResult l
  | FailedResult l
  | PrunedResult (ProgressCondition l)
           
searchcache :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> (Principal, Principal) ->
               m (Maybe (CacheSearchResult Principal))
searchcache (cur, clr) (p, q) = do
  let failedSearch = searchFailedCache (cur, clr) (p, q)
      prunedSearch = searchPrunedCache (cur, clr) (p, q)
      provedSearch = searchProvedCache (cur, clr) (p, q)
  (,,) <$> provedSearch <*> failedSearch <*> prunedSearch >>= \case
    (Just cur', _, _) -> return $ Just $ ProvedResult cur'
    (_, Just cur', _) -> return $ Just $ FailedResult cur'
    (_, _, Just pc) -> return $ Just $ PrunedResult pc
    (_, _, _) -> return Nothing

searchPrunedCache :: (HasCache (Cache Principal) m) => (Principal, Principal) -> (Principal, Principal) -> m (Maybe (ProgressCondition Principal))
searchPrunedCache (cur, clr) (p, q) = do
  cache <- getCache
  case Map.lookup (cur, clr) (view prunedCache cache) of
    Just pcache ->
      case Map.lookup (p, q) pcache of
        Just progCond -> return $ Just progCond
        Nothing -> return Nothing
    Nothing -> return Nothing

(.≽.) :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => Principal -> Principal -> m (QueryResult Principal)
p .≽. q = do
  indent <- liftLIO $ LIO $ lift $ readIORef counter
  liftLIO $ LIO $ lift $ putStr $ replicate indent ' '
  liftLIO $ LIO $ lift $ putStrLn $ show p ++ " ≽ " ++ show q
  curLab <- liftLIO getLabel
  clrLab <- liftLIO getClearance
  
  r <- searchcache (curLab, clrLab) (p, q) >>= \case
    Just (ProvedResult cur') -> do
      liftLIO $ modify $ (_1 . cur) .~ cur'
      return Success
    Just (FailedResult cur') -> do
      liftLIO $ modify $ (_1 . cur) .~ cur'
      return Failed
    Just (PrunedResult progCond) -> do
      return $ Pruned progCond
    Nothing -> do
      update (curLab, clrLab) (p, q) (Pruned (ActsFor p q))
      liftLIO $ LIO $ lift $ writeIORef counter (indent + 2)
      r <- p .≽ q
      liftLIO $ LIO $ lift $ writeIORef counter indent
      update (curLab, clrLab) (p, q) r
      return r
  liftLIO $ LIO $ lift $ putStr $ replicate indent ' '
  liftLIO $ LIO $ lift $ putStrLn $ show p ++ " ≽ " ++ show q ++ " is " ++ show r
  return r

askUser = do
  putStrLn "Type 'y' or 'n'"
  getLine >>= \case
    "y" -> return True
    "n" -> return False
    _ -> askUser

ifUserChooses s m = do
  b <- liftLIO $ LIO $ lift $ do
    indent <- readIORef counter
    putStr $ replicate indent ' '
    putStrLn $ "Try " ++ s ++ "?"
    askUser
  if b then m else return Failed

userChoice ss ms = do
  n <- liftLIO $ LIO $ lift $ do
    indent <- readIORef counter
    putStr $ replicate indent ' '
    putStrLn $ "Choose from 0 to " ++ show (length ms - 1) ++ ":"
    forM_ (List.zip ss [0..]) $ \(s, i) -> putStrLn (show i ++ ". " ++ s)
    line <- getLine
    return (read line)
  ms !! n

bot_ :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
bot_ (_, (:⊥)) = return Success
bot_ (_, (((:→) (:⊥)) :/\ ((:←) (:⊥)))) = return Success
bot_ _ = return Failed

top_ :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
top_ ((:⊤), _) = return Success
top_ ((((:→) (:⊤)) :/\ ((:←) (:⊤))), _) = return Success
top_ _ = return Failed

refl :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
refl (p, q) | p == q = return Success
refl _ = return Failed

proj :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
proj ((:→) p, (:→) q) = p .≽. q
proj ((:←) p, (:←) q) = p .≽. q
proj _ = return Failed

projR :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
projR (p, (:←) q) | p == q = return Success
projR (p, (:→) q) | p == q = return Success
projR _ = return Failed

own1 :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
own1 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. p'
own1 _ = return Failed

own2 :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
own2 (o ::: p, o' ::: p') = o .≽. o' <&&&> p .≽. (o' ::: p')
own2 _ = return Failed

conjL :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
conjL (p1 :/\ p2, p) = do
  userChoice [show p1 ++ " ≽ " ++ show p, show p2 ++ " ≽ " ++ show p] [p1 .≽. p, p2 .≽. p]
conjL _ = return Failed

conjR :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
conjR (p, p1 :/\ p2) = p .≽. p1 <&&&> p .≽. p2
conjR _ = return Failed

disjL :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
disjL (p1 :\/ p2, p) = p1 .≽. p <&&&> p2 .≽. p
disjL _ = return Failed

disjR :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
disjR (p, p1 :\/ p2) = userChoice [show p ++ " ≽ " ++ show p1, show p ++ " ≽ " ++ show p2] [p .≽. p1, p .≽. p2]
disjR _ = return Failed

reach :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> Set (Principal, Principal) -> m Bool
reach (p, q) s = do
  let pNorm = norm p
      qNorm = norm q

  cache <- getsCache $ view reachabilityCache
  (sconf, sint) <- 
    case Map.lookup s cache of
      Just (sconf, sint) -> return (sconf, sint)
      Nothing -> do
        let sconf, sint :: Set (J, J)
            (sconf, sint) = (transitive *** transitive) .
                          (atomize *** atomize) . expand $ s
        modifyCache $ over reachabilityCache (Map.insert s (sconf, sint))
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

del :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> m (QueryResult Principal)
del (p, q) = do
  indent <- liftLIO $ LIO $ lift $ readIORef counter
  h <- getState
  strat <- getStrategy
  clr <- getClearance
  r <- anyM (\stratClr ->
               let f lab = do
                     l <- liftLIO getLabel
                     liftLIO $ LIO $ lift $ putStrLn $ "Use delegation " ++ show lab ++ "?"
                     liftLIO (LIO (lift askUser)) >>= \case
                       True -> do
                         liftLIO $ LIO $ lift $ putStr $ replicate indent ' '
                         liftLIO $ LIO $ lift $ putStrLn $ "Attempting to use delegation: " ++ show lab
                         liftLIO $ LIO $ lift $ putStr $ replicate indent ' '
                         liftLIO $ LIO $ lift $ putStrLn $ "Checking " ++ show (labelOf lab ⊔ l) ++ " ⊑ " ++ show clr
                         liftLIO $ LIO $ lift $ putStr $ replicate indent ' '
                         liftLIO $ LIO $ lift $ putStrLn $ "and " ++ show (labelOf lab) ++ " ⊑ " ++ show stratClr
                         liftLIO $ LIO $ lift $ putStrLn ""
                         (,) <$> labelOf lab ⊔ l ⊑ clr <*> labelOf lab ⊑ stratClr >>= \case
                           (True, True) -> do
                             liftLIO $ LIO $ lift $ putStr $ replicate indent ' '
                             liftLIO $ LIO $ lift $ putStrLn "True!"
                             liftLIO $ LIO $ lift $ putStrLn ""
                             r <- unlabel lab
                             return $ Just r
                           _ -> do
                             liftLIO $ LIO $ lift $ putStr $ replicate indent ' '
                             liftLIO $ LIO $ lift $ putStrLn "False!"
                             liftLIO $ LIO $ lift $ putStrLn ""
                             return Nothing
                       False -> return Nothing
               in do h' <- setFilterMapM f (unH h)
                     reach (p, q) h') strat
  return $ liftB r

(.≽) :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => Principal -> Principal -> m (QueryResult Principal)
p .≽ q =
  bot_ (p, q) <|||>
  top_ (p, q) <|||>
  refl (p, q) <|||>
  userChoice ["del", "proj", "projR", "own1", "own2", "conjR", "disjL", "disjR", "conjL"]
  [ del (p, q),
    proj (p, q),
    projR (p, q),
    own1 (p, q),
    own2 (p, q),
    conjR (p, q),
    disjL (p, q),
    disjR (p, q),
    conjL (p, q) ]

(≽) :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (ToPrincipal a, ToPrincipal b) => a -> b -> m Bool
p ≽ q = lowerB <$> normalize (p %) .≽. normalize (q %)
  
instance SemiLattice Principal where
  p ⊔ q = normalize (((p /\ q) →) /\ ((p \/ q) ←))
  p ⊓ q = normalize (((p \/ q) →) /\ ((p /\ q) ←))
  
instance Label H Principal where
  type St Principal = Cache Principal
  p ⊑ q = ((q →) /\ (p ←)) ≽ ((p →) /\ (q ←))

instance MonadLIO s l m => MonadLIO s l (ReaderT r m) where
  liftLIO x = lift (liftLIO x)
  
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
                        ([],_)              -> f : mergeWith op fs
                        (updated,untouched) -> mergeWith op (updated ++ untouched)

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

class ToPrincipal c where
  (%) :: c -> Principal

instance ToPrincipal JNF where
  (%) x = ((confidentiality x) →) :/\ ((integrity x) ←)

instance ToPrincipal Principal where
  (%) = id

instance ToPrincipal [Char] where
  (%) = Name

instance ToPrincipal J where
  (%) (J (listview -> [m])) = (%) m
  (%) (J (setview -> Just (m, ms))) = (%) m :/\ (%) (J ms)

instance ToPrincipal M where
  (%) (M (listview -> [l])) = (%) l
  (%) (M (setview -> Just (l, ls))) = (%) l :\/ (%) (M ls)

instance ToPrincipal L where
  (%) (N s) = (%) s
  (%) T = (:⊤)
  (%) B = (:⊥)
  (%) (p :.: q) = (%) p ::: (%) q

(/\) :: (ToPrincipal a, ToPrincipal b) => a -> b -> Principal
a /\ b = (a %) :/\ (b %)
infixr 7 /\

(\/) :: (ToPrincipal a, ToPrincipal b) => a -> b -> Principal
a \/ b = (a %) :\/ (b %)
infixr 7 \/

(→) :: (ToPrincipal a) => a -> Principal
(→) a = (:→) (a %)

(←) :: (ToPrincipal a) => a -> Principal
(←) a = (:←) (a %)

(.:) :: (ToPrincipal a, ToPrincipal b) => a -> b -> Principal
a .: b = (a %) ::: (b %)

type FLAM = Principal

bot :: Principal
bot = (:→) (:⊥) :/\ (:←) (:⊤)

top :: Principal
top = (:→) (:⊤) :/\ (:←) (:⊥)

newtype FLAMIO a = FLAMIO { unFLAMIO :: StateT (Cache Principal) (LIO H FLAM) a }
  deriving (Functor, Applicative, Monad)

instance HasCache (Cache Principal) FLAMIO where
  getCache = FLAMIO get
  putCache = FLAMIO . put

instance MonadLIO H FLAM FLAMIO where
  liftLIO = FLAMIO . liftLIO

instance HasCache (Cache l) m => HasCache (Cache l) (StateT s m) where
  getCache = lift getCache
  putCache = lift . putCache
  
addDelegate :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> Principal -> m ()
addDelegate (p, q) l = do
  h <- liftLIO getState
  lab <- label l (normalize p, normalize q)
  modifyCache $ prunedCache .~ Map.empty
  liftLIO $ setState (H $ Set.insert lab (unH h))

removeDelegate :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => (Principal, Principal) -> Principal -> m ()
removeDelegate (p, q) l = do
  h <- liftLIO getState
  lab <- label l (p, q)
  modifyCache $ prunedCache .~ Map.empty
  liftLIO $ setState (H $ Set.delete lab (unH h))

setStrategy :: (MonadLIO H FLAM m, HasCache (Cache Principal) m) => Strategy Principal -> m ()
setStrategy ls = do
  modifyCache $ prunedCache .~ Map.empty
  liftLIO $ modify $ (_3 .~ ls)

runFLAM :: FLAMIO a -> LIO H FLAM a
runFLAM a = evalStateT (unFLAMIO a) emptyCache
