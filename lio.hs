{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitForAll, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TemplateHaskell, FunctionalDependencies, LambdaCase, TypeFamilies, LiberalTypeSynonyms #-}
module LIO where

import Control.Monad.State
import Data.IORef
import Control.Lens
import Control.Monad.State.Class
import Control.Monad.Catch

{- We need to seperate these two classes in order to call (⊔) and (⊔)
   without getting an ambiguity error since these two functions
   do not mention the state -}
class SemiLattice l where
  (⊔) :: l -> l -> l
  (⊓) :: l -> l -> l

data BoundedLabel l = BoundedLabel { _cur :: l, _clearance :: l }
  deriving (Eq, Ord, Show)

makeLenses ''BoundedLabel

type Strategy l = [l]

newtype LIO s l a = LIO { unLIO :: StateT (BoundedLabel l, s, Strategy l) IO a }

class Monad m => MonadLIO s l m | m -> s l where
  liftLIO :: LIO s l a -> m a

instance Label s l => MonadLIO s l (LIO s l) where
  liftLIO = id

instance (Label s l, MonadLIO s l m) => MonadLIO s l (StateT st m) where
  liftLIO m = StateT $ \st -> do
    x <- liftLIO m
    return (x, st)

class Monad m => HasCache c m | m -> c where
  getCache :: m c
  putCache :: c -> m ()
  
  modifyCache :: (c -> c) -> m ()
  modifyCache f = do
    c <- getCache
    putCache (f c)

  getsCache :: (c -> a) -> m a
  getsCache f = do
    c <- getCache
    return $ f c

class (Show l, SemiLattice l) => Label s l where
  type St l
  (⊑) :: (MonadLIO s l m, HasCache (St l) m) => l -> l -> m Bool

instance Label s l => Functor (LIO s l) where
  fmap f (LIO x) = LIO (fmap f x)

instance Label s l => Monad (LIO s l) where
  return x = LIO (return x)
  (LIO x) >>= f = LIO . StateT $ \s -> do
    (y, s') <- runStateT x s
    runStateT (unLIO $ f y) s'

instance Label s l => Applicative (LIO s l) where
  pure = return
  (<*>) = ap

instance Label s l => MonadState (BoundedLabel l, s, Strategy l) (LIO s l) where
  get = LIO . StateT $ \s -> return (s, s)
  put s = LIO . StateT $ const (return ((), s))
  
getLabel :: (MonadLIO s l m, Label s l) => m l
getLabel = liftLIO $ gets $ view $ _1 . cur

getClearance :: (MonadLIO s l m, Label s l) => m l
getClearance = liftLIO $ gets $ view $ _1 . clearance

getState :: (MonadLIO s l m, Label s l) => m s
getState = liftLIO $ gets $ view _2

setState :: (MonadLIO s l m, Label s l) => s -> m ()
setState s = liftLIO $ modify $ _2 .~ s

data Labeled l a = Labeled { _labeledLab :: l, _labeledVal :: a }

makeLenses ''Labeled

raise :: (MonadLIO s l m, Label s l, HasCache (St l) m) => String -> l -> m ()
raise msg l = do
  l' <- liftLIO $ gets $ view _1
  b <- view cur l' ⊔ l ⊑ view clearance l'
  unless b $
    fail ("IFC violation (" ++ msg ++ "): " ++
           show (view cur l') ++ " ⊔ " ++ show l  ++
           " ⊑ " ++ show (view clearance l'))
  liftLIO $ modify $ over (_1 . cur) (l ⊔)
  
(<&&>) :: (Monad m) => m Bool -> m Bool -> m Bool
(<&&>) m1 m2 =
  m1 >>= \case
    True -> m2
    False -> return False
infixr 8 <&&>

(<||>) :: (Monad m) => m Bool -> m Bool -> m Bool
(<||>) m1 m2 =
  m1 >>= \case
    True -> return True
    False -> m2
infixr 7 <||>

(∈) :: (MonadLIO s l m, Label s l, HasCache (St l) m) => l -> BoundedLabel l -> m Bool
(∈) l lab = view cur lab ⊑ l <&&> l ⊑ view clearance lab

label :: (MonadLIO s l m, Label s l, HasCache (St l) m) => l -> a -> m (Labeled l a)
label l x = do
  lab <- liftLIO $ gets $ view _1
  b <- l ∈ lab
  unless b $
    fail ("IFC violation (label): " ++
           show (view cur lab) ++
           " ⊑ " ++ show l ++
           " ⊑ " ++ show (view clearance lab))
  return $ Labeled {_labeledLab = l, _labeledVal = x }

unlabel :: (MonadLIO s l m, Label s l, HasCache (St l) m) => Labeled l a -> m a
unlabel lab = do
  raise "unlabel" (labelOf lab)
  return (view labeledVal lab)

toLabeled :: (MonadLIO s l m, Label s l, HasCache (St l) m) => l -> m a -> m (Labeled l a)
toLabeled l m = do
  l' <- liftLIO $ gets $ view _1
  res <- m
  l'' <- liftLIO $ gets $ view $ _1 . cur
  b <- l'' ⊑ l
  unless b $ do
    fail ("IFC violation (toLabeled): " ++ show l'' ++ " ⊑ " ++ show l)
  liftLIO $ modify $ (_1 .~ l')
  label l res

toLabeled_ :: (MonadLIO s l m, Label s l, HasCache (St l) m) => l -> m a -> m ()
toLabeled_ l m = do
  l' <- liftLIO $ gets $ view _1
  res <- m
  l'' <- liftLIO $ gets $ view $ _1 . cur
  b <- l'' ⊑ l
  unless b $ do
    fail ("IFC violation (toLabeled_): " ++ show l'' ++ " ⊑ " ++ show l)
  liftLIO $ modify $ (_1 .~ l')

getStrategy :: (MonadLIO s l m, Label s l, HasCache (St l) m) => m (Strategy l)
getStrategy = liftLIO $ gets $ view _3

labelOf :: Labeled l a -> l
labelOf = view labeledLab

newtype LIORef l a = LIORef { unLIORef :: Labeled l (IORef a) }

newRef :: (MonadLIO s l m, Label s l, HasCache (St l) m) => l -> a -> m (LIORef l a)
newRef l x = do
  lab <- liftLIO $ gets $ view _1
  b <- l ∈ lab
  liftLIO . LIO . StateT $ \(lab, s, strat) -> do
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show l ++
           " ⊑ " ++ show (view clearance lab))
  r <- newIORef x
  return (LIORef (Labeled {_labeledLab = l, _labeledVal = r}), (lab, s, strat))

readRef :: (MonadLIO s l m, Label s l, HasCache (St l) m) => LIORef l a -> m a
readRef (LIORef lref) =
  raise "readRef" (labelOf lref) >> unlabel lref >>= \r -> do
  liftLIO . LIO . StateT $ \s -> do
    x <- readIORef r
    return (x, s)

(!) :: (MonadLIO s l m, Label s l, HasCache (St l) m) => LIORef l a -> m a
(!) = readRef

writeRef :: (MonadLIO s l m, Label s l, HasCache (St l) m) => LIORef l a -> a -> m ()
writeRef (LIORef lref) x = do
  lab <- liftLIO $ gets $ view _1
  b <- labelOf lref ∈ lab
  unless b $
    fail ("IFC violation: " ++
           show (view cur lab) ++
           " ⊑ " ++ show (labelOf lref) ++
           " ⊑ " ++ show (view clearance lab))
    
  unlabel lref >>= \ref ->
    liftLIO . LIO . StateT $ \s -> do
      writeIORef ref x
      return ((), s)

(.=) :: (MonadLIO s l m, Label s l, HasCache (St l) m) => LIORef l a -> a -> m ()
(.=) = writeRef

{- These weird instances are needed for networking -}

instance Label s l => MonadThrow (LIO s l) where
  throwM = LIO . throwM

instance Label s l => MonadCatch (LIO s l) where
  catch (LIO m) f = LIO $ catch m (unLIO . f)

instance Label s l => MonadMask (LIO s l) where
  mask a = LIO $ mask $ \u -> unLIO (a $ q u)
    where q u (LIO b) = LIO (u b)
    
  uninterruptibleMask a = LIO $ uninterruptibleMask $ \u -> unLIO (a $ q u)
    where q u (LIO b) = LIO (u b)

  generalBracket acquire release use = LIO $ generalBracket
    (unLIO acquire)
    (\resource exitCase -> unLIO (release resource exitCase))
    (\resource -> unLIO (use resource))
