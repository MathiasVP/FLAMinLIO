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

class Monad m => MonadLIO s l m | m -> s l where
  liftLIO :: LIO s l a -> m a

instance Label t s l => MonadLIO s l (LIO s l) where
  liftLIO = id

instance (Label t s l, MonadLIO s l m) => MonadLIO s l (StateT st m) where
  liftLIO m = StateT $ \st -> do
    x <- liftLIO m
    return (x, st)

class (Show l, SemiLattice l, MonadTrans t, Monad (t (LIO s l))) => Label t s l | s l -> t where
  (.⊑) :: MonadLIO s l m => l -> l -> t m Bool
  run :: MonadLIO s l m => t m a -> m a

(⊑) :: (MonadLIO s l m, Label t s l) => l -> l -> m Bool
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
  
getLabel :: (MonadLIO s l m, Label t s l) => m l
getLabel = liftLIO $ gets $ view $ _1 . cur

getClearance :: (MonadLIO s l m, Label t s l) => m l
getClearance = liftLIO $ gets $ view $ _1 . clearance

getState :: (MonadLIO s l m, Label t s l) => m s
getState = liftLIO $ gets $ view _2

setState :: (MonadLIO s l m, Label t s l) => s -> m ()
setState s = liftLIO $ modify $ _2 .~ s

data Labeled l a = Labeled { _labeledLab :: l, _labeledVal :: a }

makeLenses ''Labeled

raise :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> t m ()
raise l = do
  l' <- lift $ liftLIO $ gets $ view _1
  s <- lift getState
  b <- (view cur l') ⊔ l .⊑ view clearance l'
  unless b $
    fail ("IFC violation: " ++
           show (view cur l' ⊔ l) ++
           " ⊑ " ++ show (view clearance l'))
  lift $ liftLIO $ modify $ over (_1 . cur) ((⊔) l)

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

(∈) :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> BoundedLabel l -> t m Bool
(∈) l lab = (view cur lab .⊑ l) <&&> (l .⊑ view clearance lab)

label' :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> a -> t m (Labeled l a)
label' l x = do
  lab <- lift $ liftLIO $ gets $ view _1
  b <- l ∈ lab
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show l ++
           " ⊑ " ++ show (view clearance lab))
  return $ Labeled {_labeledLab = l, _labeledVal = x }

label :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> a -> m (Labeled l a)
label l a = run (label' l a)

unlabel' :: (MonadLIO s l m, Label t s l, Monad (t m)) => Labeled l a -> t m a
unlabel' lab = do
  raise (view labeledLab lab)
  return (view labeledVal lab)

unlabel :: (MonadLIO s l m, Label t s l, Monad (t m)) => Labeled l a -> m a
unlabel = run . unlabel'

toLabeled' :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> m a -> t m (Labeled l a)
toLabeled' l m = do
  l' <- lift $ liftLIO $ gets $ view _1
  res <- lift $ m
  l'' <- lift $ liftLIO $ gets $ view $ _1 . cur
  b <- l'' .⊑ l
  unless b $ do
    fail ("IFC violation: " ++ show l'' ++ " ⊑ " ++ show l)
  lift $ liftLIO $ modify $ (_1 .~ l')
  label' l res

toLabeled :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> m a -> m (Labeled l a)
toLabeled l x = run (toLabeled' l x)

labelOf :: Labeled l a -> l
labelOf = view labeledLab

newtype LIORef l a = LIORef { unLIORef :: Labeled l (IORef a) }

newRef' :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> a -> t m (LIORef l a)
newRef' l x = do
  lab <- lift $ liftLIO $ gets $ view _1
  b <- l ∈ lab
  lift . liftLIO . LIO . StateT $ \(lab, s) -> do
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show l ++
           " ⊑ " ++ show (view clearance lab))
  r <- newIORef x
  return (LIORef (Labeled {_labeledLab = l, _labeledVal = r}), (lab, s))

newRef :: (MonadLIO s l m, Label t s l, Monad (t m)) => l -> a -> m (LIORef l a)
newRef l x = run (newRef' l x)

readRef :: (MonadLIO s l m, Label t s l, Monad (t m)) => LIORef l a -> t m a
readRef (LIORef lref) =
  raise (labelOf lref) >> unlabel' lref >>= \r -> do
  lift . liftLIO . LIO . StateT $ \s -> do
    x <- readIORef r
    return (x, s)

(!) :: (MonadLIO s l m, Label t s l, Monad (t m)) => LIORef l a -> m a
(!) = run . readRef

writeRef :: (MonadLIO s l m, Label t s l, Monad (t m)) => LIORef l a -> a -> t m ()
writeRef (LIORef lref) x = do
  lab <- lift $ liftLIO $ gets $ view _1
  b <- labelOf lref ∈ lab
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show (labelOf lref) ++
           " ⊑ " ++ show (view clearance lab))
    
  unlabel' lref >>= \ref ->
    lift . liftLIO . LIO . StateT $ \s -> do
      writeIORef ref x
      return ((), s)

(.=) :: (MonadLIO s l m, Label t s l, Monad (t m)) => LIORef l a -> a -> m ()
(.=) r = run . writeRef r
