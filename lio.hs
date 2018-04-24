{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitForAll, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TemplateHaskell, FunctionalDependencies, LambdaCase #-}
module LIO where

import Control.Monad.State
import Data.IORef
import Control.Lens

{- We need to seperate these two classes in order to call (⊔) and (⊔)
   without getting an ambiguity error since these two functions
   do not mention the state -}
class SemiLattice l where
  (⊔) :: l -> l -> l
  (⊓) :: l -> l -> l

data BoundedLabel l = BoundedLabel { _cur :: l, _clearance :: l }
  deriving (Eq, Ord, Show)

makeLenses ''BoundedLabel

newtype LIO s l a = LIO { unLIO :: StateT (BoundedLabel l, s) IO a }

class (Show l, SemiLattice l, MonadTrans t, Monad (t (LIO s l))) => Label t s l | s l -> t where
  (.⊑) :: l -> l -> t (LIO s l) Bool
  run :: t (LIO s l) a -> LIO s l a

(⊑) :: Label t s l => l -> l -> LIO s l Bool
p ⊑ q = run (p .⊑ q)

instance Label t s l => Functor (LIO s l) where
  fmap f (LIO x) = LIO (fmap f x)

instance Label t s l => Monad (LIO s l) where
  return x = LIO (return x)
  (LIO x) >>= f = LIO . StateT $ \s -> do
    (y, s') <- runStateT x s
    runStateT (unLIO $ f y) s'

instance Label t s l => Applicative (LIO s l) where
  pure = return
  (<*>) = ap

instance Label t s l => MonadState (BoundedLabel l, s) (LIO s l) where
  get = LIO . StateT $ \s -> return (s, s)
  put s = LIO . StateT $ const (return ((), s))
  
getLabel :: Label t s l => LIO s l l
getLabel = gets $ view $ _1 . cur

getClearance :: Label t s l => LIO s l l
getClearance = gets $ view $ _1 . clearance

getState :: Label t s l => LIO s l s
getState = gets $ view _2

setState :: Label t s l => s -> LIO s l ()
setState s = modify $ _2 .~ s

data Labeled l a = Labeled { _labeledLab :: l, _labeledVal :: a }

makeLenses ''Labeled

raise :: (Label t s l) => l -> t (LIO s l) ()
raise l = do
  l' <- lift $ gets $ view _1
  s <- lift getState
  b <- (view cur l') ⊔ l .⊑ view clearance l'
  unless b $
    fail ("IFC violation: " ++
           show (view cur l' ⊔ l) ++
           " ⊑ " ++ show (view clearance l'))
  lift $ modify $ over (_1 . cur) ((⊔) l)

(<&&>) :: Monad m => m Bool -> m Bool -> m Bool
(<&&>) m1 m2 =
  m1 >>= \case
    True -> m2
    False -> return False
infixr 8 <&&>

(<||>) :: Monad m => m Bool -> m Bool -> m Bool
(<||>) m1 m2 =
  m1 >>= \case
    True -> return True
    False -> m2
infixr 7 <||>

(∈) :: Label t s l => l -> BoundedLabel l -> t (LIO s l) Bool
(∈) l lab = (view cur lab .⊑ l) <&&> (l .⊑ view clearance lab)

label' :: Label t s l => l -> a -> t (LIO s l) (Labeled l a)
label' l x = do
  lab <- lift $ gets $ view _1
  b <- l ∈ lab
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show l ++
           " ⊑ " ++ show (view clearance lab))
  return $ Labeled {_labeledLab = l, _labeledVal = x }

label :: Label t s l => l -> a -> LIO s l (Labeled l a)
label l a = run (label' l a)

unlabel' :: Label t s l => Labeled l a -> t (LIO s l) a
unlabel' lab = do
  raise (view labeledLab lab)
  return (view labeledVal lab)

unlabel :: Label t s l => Labeled l a -> LIO s l a
unlabel = run . unlabel'

toLabeled' :: Label t s l => l -> LIO s l a -> t (LIO s l) (Labeled l a)
toLabeled' l m = do
  l' <- lift $ gets $ view _1
  res <- lift m
  l'' <- lift $ gets $ view $ _1 . cur
  b <- l'' .⊑ l
  unless b $ do
    fail ("IFC violation: " ++ show l'' ++ " ⊑ " ++ show l)
  lift $ modify $ (_1 .~ l')
  label' l res

toLabeled :: Label t s l => l -> LIO s l a -> LIO s l (Labeled l a)
toLabeled l x = run (toLabeled' l x)

labelOf :: Labeled l a -> l
labelOf = view labeledLab

newtype LIORef l a = LIORef { unLIORef :: Labeled l (IORef a) }

newRef' :: Label t s l => l -> a -> t (LIO s l) (LIORef l a)
newRef' l x = do
  lab <- lift $ gets $ view _1
  b <- l ∈ lab
  lift . LIO . StateT $ \(lab, s) -> do
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show l ++
           " ⊑ " ++ show (view clearance lab))
  r <- newIORef x
  return (LIORef (Labeled {_labeledLab = l, _labeledVal = r}), (lab, s))

newRef :: Label t s l => l -> a -> LIO s l (LIORef l a)
newRef l x = run (newRef' l x)

readRef :: Label t s l => LIORef l a -> t (LIO s l) a
readRef (LIORef lref) =
  raise (labelOf lref) >> unlabel' lref >>= \r -> do
  lift . LIO . StateT $ \s -> do
    x <- readIORef r
    return (x, s)

(!) :: Label t s l => LIORef l a -> LIO s l a
(!) = run . readRef

writeRef :: Label t s l => LIORef l a -> a -> t (LIO s l) ()
writeRef (LIORef lref) x = do
  lab <- lift $ gets $ view _1
  b <- labelOf lref ∈ lab
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show (labelOf lref) ++
           " ⊑ " ++ show (view clearance lab))
    
  unlabel' lref >>= \ref ->
    lift . LIO . StateT $ \s -> do
      writeIORef ref x
      return ((), s)

(.=) :: Label t s l => LIORef l a -> a -> LIO s l ()
(.=) r = run . writeRef r
