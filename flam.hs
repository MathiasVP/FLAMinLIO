{-# LANGUAGE FlexibleInstances, ViewPatterns, PostfixOperators, OverloadedStrings, MultiParamTypeClasses, ExplicitForAll, ScopedTypeVariables, LambdaCase, MonadComprehensions #-}
module FLAM(Principal(..), (≽), (⊑), H(..), FLAM, bot, top, (%), (/|\), (\|/), (→), (←)) where

import LIO
import TCB()
import qualified Data.List as List
import qualified Data.Set.Monad as Set
import Data.Set.Monad(Set, (\\))
import Data.Either
import Data.String
import Control.Monad.State
import Control.Applicative
import qualified Data.Maybe as Maybe
import Control.Monad.Reader
import Control.Monad.Trans.Maybe
import Control.Arrow
import Control.Monad.Loops
import Control.Lens.Tuple
import Control.Lens

listview :: Ord a => Set a -> [a]
listview = Set.toList

setview :: Ord a => Set a -> Maybe (a, Set a)
setview = Set.minView

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
  
instance IsString Principal where
  fromString = Name

instance SemiLattice Principal where
  p ⊔ q = ((p :/\ q) :→) :/\ ((p :\/ q) :←)
  p ⊓ q = ((p :\/ q) :→) :/\ ((p :/\ q) :←)

newtype H = H { unH :: Set (Labeled Principal (Principal, Principal)) }

type Trace = (Set (Principal, Principal), Int)

setMapM :: (Ord a, Ord b, Monad m) => (a -> m b) -> Set a -> m (Set b)
setMapM f s = do
  s' <- mapM f (Set.toList s)
  return $ Set.fromList s'

setFilterM :: (Ord a, Monad m) => (a -> m Bool) -> Set a -> m (Set a)
setFilterM f s = do
  s' <- filterM f (Set.toList s)
  return $ Set.fromList s'

(.≽.) :: Principal -> Principal -> ReaderT Trace (LIO H FLAM) Bool
p .≽. q = do
  (_, indent) <- ask
  lift $ LIO . StateT $ \s -> do
    putStr $ replicate indent ' '
    putStrLn $ "Goal:     " ++ show p ++ " ≽ " ++ show q
    return ((), s)
  asks (Set.member (p, q) . view _1) >>= \case
    True -> do
      lift $ LIO . StateT $ \s -> do
        putStr $ replicate indent ' '
        putStrLn $ "Cycle:    " ++ show p ++ " ≽ " ++ show q
        return ((), s)
      return False
    False -> do
      r <- local (\(tr, n) -> (Set.insert (p, q) tr, n + 2)) $ p .≽ q
      lift $ LIO . StateT $ \s -> do
        putStr $ replicate indent ' '
        putStrLn $ "Finished: " ++ show p ++ " ≽ " ++ show q ++ " is " ++ show r
        return ((), s)
      return r

bot_ :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
bot_ (_, (:⊥)) = return True
bot_ _ = return False

top_ :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
top_ ((:⊤), _) = return True
top_ _ = return False

refl :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
refl (p, q) | p == q = return True
refl _ = return False

proj :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
proj ((:→) p, (:→) q) = p .≽. q
proj ((:←) p, (:←) q) = p .≽. q
proj _ = return False

projR :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
projR (p, (:←) q) | p == q = return True
projR (p, (:→) q) | p == q = return True
projR _ = return False

own1 :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
own1 (o ::: p, o' ::: p') = o .≽. o' <&&> p .≽. p'
own1 _ = return False

own2 :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
own2 (o ::: p, o' ::: p') = o .≽. o' <&&> p .≽. (o' ::: p')
own2 _ = return False

conjL :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
conjL (p1 :/\ p2, p) = p1 .≽. p <||> p2 .≽. p
conjL _ = return False

conjR :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
conjR (p, p1 :/\ p2) = p .≽. p1 <&&> p .≽. p2
conjR _ = return False

disjL :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
disjL (p1 :\/ p2, p) = p .≽. p1 <&&> p .≽. p2
disjL _ = return False

disjR :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
disjR (p, p1 :\/ p2) = p1 .≽. p <||> p2 .≽. p
disjR _ = return False

reach :: (Principal, Principal) -> Set (Principal, Principal) -> Bool
reach (p, q) s =
  (confidentiality pNorm, confidentiality qNorm) `Set.member` sconf &&
  (integrity pNorm, integrity qNorm) `Set.member` sint
  where pNorm = norm p
        qNorm = norm q
        sconf, sint :: Set (J, J)
        (sconf, sint) = (transitive *** transitive) .
                        (atomize *** atomize) . expand $ s

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
    expand' = Set.foldr' (\(p, J q) -> Set.union [(p', q')
                                                 | p' <- (⊗) p, q' <- q]) Set.empty

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
atomize s = [(J p', J (Set.singleton (M q'))) |
              (J p, M q) <- s, p' <- powerset p, q' <- powerset q]

{- Compute transitive closure of a set -}
transitive :: (Ord a, Eq a) => Set (a, a) -> Set (a, a)
transitive s
  | s == s' = s
  | otherwise  = transitive s'
  where s' = s `Set.union` [(a, c) | (a, b) <- s, (b', c) <- s, b == b']

{- Join of meets into Meet of joins -}
(⊗) :: J -> Set J
(⊗) (J ms) = [J . Set.fromList $ map mkM ps |
              ps <- sequence [bs | M bs <- Set.toList ms]]
  where mkM = M . Set.singleton

del :: (Principal, Principal) -> ReaderT Trace (LIO H FLAM) Bool
del (p, q) = do
  clr <- lift getClearance
  l <- lift getLabel
  h <- lift getState
  {- We have to check labelOf lab ⊔ l instead of labelOf lab.
     To see an example of why, consider the (minimal) example:

  setState (H $ Set.fromList [Labeled { _labeledLab = top,
                                        _labeledVal = (Name "p", Name "q") }])
  run $ (((:⊤) →) :/\ ((:⊤) ←)) .≽. (((:⊤) →) :/\ ((:⊥) ←))

  or the example:

  setState (H $ Set.fromList [Labeled { _labeledLab = top,
                                        _labeledVal = (Name "p", Name "q") }])
  run $ ((:→) (Name "p")) .≽. ((:→) (Name "q"))
-}
  h' <- setFilterM (\lab -> labelOf lab ⊔ l .⊑ clr) >=>
        setMapM (\lab -> unlabel' lab) $ (unH h)
  if reach (p, q) h' then return True else return False
  
(.≽) :: Principal -> Principal -> ReaderT Trace (LIO H FLAM) Bool
p .≽ q =
  bot_ (p, q) <||>
    top_ (p, q) <||>
    refl (p, q) <||>
    proj (p, q) <||>
    projR (p, q) <||>
    own1 (p, q) <||>
    own2 (p, q) <||>
    conjL (p, q) <||>
    conjR (p, q) <||>
    disjL (p, q) <||>
    disjR (p, q) <||>
    del (p, q)

(≽) :: Principal -> Principal -> LIO H FLAM Bool
p ≽ q = run (p .≽ q)

instance Label (ReaderT Trace) H Principal where
  p .⊑ q = normalize ((q :→) :/\ (p :←)) .≽. normalize ((p :→) :/\ (q :←))
  run query = runReaderT query (Set.empty, 0)

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

mSingleton :: L -> M
mSingleton b = M $ Set.singleton b

jSingleton :: L -> J
jSingleton b = J $ Set.singleton $ mSingleton b

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

(/|\) :: (ToPrincipal a, ToPrincipal b) => a -> b -> Principal
a /|\ b = (a %) :/\ (b %)
infixr 7 /|\

(\|/) :: (ToPrincipal a, ToPrincipal b) => a -> b -> Principal
a \|/ b = (a %) :\/ (b %)
infixr 7 \|/

(→) :: (ToPrincipal a) => a -> Principal
(→) a = (:→) (a %)

(←) :: (ToPrincipal a) => a -> Principal
(←) a = (:←) (a %)

type FLAM = Principal

bot :: Principal
bot = (:→) (:⊥) :/\ (:←) (:⊤)

top :: Principal
top = (:→) (:⊤) :/\ (:←) (:⊥)
