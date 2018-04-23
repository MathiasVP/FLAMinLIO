{-# LANGUAGE FlexibleInstances #-}
module DC where

import LIO
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Test.QuickCheck as QC
import Test.QuickCheck(Arbitrary)

newtype Principal = Principal String
  deriving (Eq, Ord, Show)

instance Arbitrary Principal where
    arbitrary = Principal <$> QC.arbitrary

newtype Disjunction = Disjunction (Set Principal)
  deriving (Eq, Ord, Show)

instance Arbitrary Disjunction where
  arbitrary = Disjunction <$> QC.arbitrary

class Logic a where
  true :: a
  false :: a
  (==>) :: a -> a -> Bool
  (/\) :: a -> a -> a
  (\/) :: a -> a -> a
  
  (<==>) :: a -> a -> Bool
  x <==> y = x ==> y && y ==> x

instance Logic Disjunction where
  true = undefined
  false = Disjunction Set.empty
  Disjunction ps1 ==> Disjunction ps2 = ps1 `Set.isSubsetOf` ps2
  Disjunction ps1 /\ Disjunction ps2 = Disjunction (ps1 `Set.intersection` ps2)
  Disjunction ps1 \/ Disjunction ps2 = Disjunction (ps1 `Set.union` ps2)

instance Monoid Disjunction where
  mempty = false
  mappend (Disjunction x) (Disjunction y) = Disjunction (x `Set.union` y)

newtype CNF = CNF (Set Disjunction)
  deriving (Eq, Ord, Show)

instance Arbitrary CNF where
  arbitrary = CNF <$> QC.arbitrary

setAny :: (a -> Bool) -> Set a -> Bool
setAny prd = Set.foldr' (\a -> (prd a ||)) False

setAll :: (a -> Bool) -> Set a -> Bool
setAll prd = Set.foldr' (\a -> (prd a &&)) True

instance Logic CNF where
  true = CNF Set.empty
  false = CNF $ Set.singleton false
  c ==> (CNF ds) = setAll (c `cImplies`) ds
    where cImplies (CNF ds) d = setAny (==> d) ds
  CNF ds1 /\ CNF ds2 = CNF (ds1 `Set.union` ds2)
  CNF ds1 \/ CNF ds2 = CNF . Set.fromList $
                          [Disjunction (d1 `Set.union` d2) |
                            Disjunction d1 <- Set.toList ds1,
                            Disjunction d2 <- Set.toList ds2]

insert :: Disjunction -> CNF -> CNF
insert dnew c@(CNF ds)
  | setAny (==> dnew) ds = c
  | otherwise = CNF $ Set.insert dnew $ Set.filter (not . (dnew ==>)) ds

instance Monoid CNF where
  mempty = true
  mappend c (CNF ds) = Set.foldr insert c ds

data DCLabel = DCLabel { confidentiality :: CNF, integrity :: CNF }
  deriving (Eq, Ord, Show)

instance Label DCLabel where
  DCLabel c1 i1 ⊑ DCLabel c2 i2 = c2 ==> c1 && i1 ==> i2
  DCLabel c1 i1 ⊔ DCLabel c2 i2 = DCLabel (c1 /\ c2) (i1 \/ i2)
  DCLabel c1 i1 ⊓ DCLabel c2 i2  = DCLabel (c1 \/ c2) (i1 /\ i2)

instance Arbitrary DCLabel where
  arbitrary = DCLabel <$> QC.arbitrary <*> QC.arbitrary

class ToCNF c where
  toCNF :: c -> CNF

instance ToCNF CNF where
  toCNF = id

instance ToCNF Disjunction where
  toCNF = CNF . Set.singleton 

instance ToCNF Principal where
  toCNF = CNF . Set.singleton . Disjunction . Set.singleton

instance ToCNF [Char] where
  toCNF = toCNF . Principal

instance ToCNF Bool where
  toCNF True = true
  toCNF False = false

(%%) :: (ToCNF a, ToCNF b) => a -> b -> DCLabel
a %% b = toCNF a `DCLabel` toCNF b
infix 6 %%

(/|\) :: (ToCNF a, ToCNF b) => a -> b -> CNF
a /|\ b = toCNF a /\ toCNF b
infixr 7 /|\

(\|/) :: (ToCNF a, ToCNF b) => a -> b -> CNF
a \|/ b = toCNF a \/ toCNF b
infixr 7 \|/

-- Property based tests follow
conjElim1 :: CNF -> CNF -> Bool
conjElim1 c1 c2 = (c1 /\ c2) ==> c1

conjElim2 :: CNF -> CNF -> Bool
conjElim2 c1 c2 = (c1 /\ c2) ==> c2

conjComm :: CNF -> CNF -> Bool
conjComm c1 c2 = (c1 /\ c2) <==> (c2 /\ c1)

disjIntro1 :: CNF -> CNF -> Bool
disjIntro1 c1 c2 = c1 ==> (c1 \/ c2)

disjIntro2 :: CNF -> CNF -> Bool
disjIntro2 c1 c2 = c2 ==> (c1 \/ c2)

disjComm :: CNF -> CNF -> Bool
disjComm c1 c2 = (c1 \/ c2) <==> (c2 \/ c1)

false_is_initial :: CNF -> Bool
false_is_initial c = false ==> c

true_is_terminal :: CNF -> Bool
true_is_terminal c = c ==> true
