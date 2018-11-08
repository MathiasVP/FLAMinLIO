{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitForAll, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TemplateHaskell, FunctionalDependencies, LambdaCase, TypeFamilies, LiberalTypeSynonyms #-}
module Lib.LIO where

import Control.Monad.State
import Data.IORef
import Control.Lens
import Control.Monad.State.Class
import Control.Monad.Catch
import Control.Monad.Reader
import GHC.Exts(Constraint)
import Algebra.PartialOrd
import GHC.Generics hiding (C)
import qualified Data.List as List
import Data.Binary
import Control.Concurrent.Forkable

class ToLabel a l where
  (%) :: a -> l

instance ToLabel l l where
  (%) = id

{- We need to seperate these two classes in order to call (⊔) and (⊔)
   without getting an ambiguity error since these two functions
   do not mention the state -}
class SemiLattice l where
  (.⊔.) :: l -> l -> l
  (.⊓.) :: l -> l -> l

(⊔) :: (SemiLattice l, ToLabel a l, ToLabel b l) => a -> b -> l
a ⊔ b = (%) a .⊔. (%) b

(⊓) :: (SemiLattice l, ToLabel a l, ToLabel b l) => a -> b -> l
a ⊓ b = (%) a .⊓. (%) b

data BoundedLabel l = BoundedLabel { _cur :: l, _clearance :: l }
  deriving (Eq, Ord, Show)

makeLenses ''BoundedLabel
  
newtype Strategy l = Strategy { unStrategy :: [l] }
  deriving (Eq, Ord, Functor, Generic, Show)

instance Eq l => PartialOrd (Strategy l) where
  x `leq` y = unStrategy x `List.isPrefixOf` unStrategy y

newtype LIO l a = LIO { unLIO :: StateT (BoundedLabel l, Strategy l) IO a }

class (Monad m, Label l) => MonadLIO l m | m -> l where
  liftLIO :: LIO l a -> m a

instance Label l => MonadLIO l (LIO l) where
  liftLIO = id

instance MonadLIO l m => MonadLIO l (StateT st m) where
  liftLIO m = StateT $ \st -> do
    x <- liftLIO m
    return (x, st)

instance MonadLIO l m => MonadLIO l (ReaderT r m) where
  liftLIO m = ReaderT (const $ liftLIO m)
  
class (Show l, SemiLattice l) => Label l where
  type C l :: (* -> *) -> Constraint
  (⊑) :: (MonadLIO l m, C l m, ToLabel a l, ToLabel b l) =>
         a -> b -> m Bool

instance Label l => Functor (LIO l) where
  fmap f (LIO x) = LIO (fmap f x)

instance Label l => Monad (LIO l) where
  return x = LIO (return x)
  (LIO x) >>= f = LIO . StateT $ \s -> do
    (y, s') <- runStateT x s
    runStateT (unLIO $ f y) s'

instance Label l => Applicative (LIO l) where
  pure = return
  (<*>) = ap

instance Label l => MonadState (BoundedLabel l, Strategy l) (LIO l) where
  get = LIO . StateT $ \s -> return (s, s)
  put s = LIO . StateT $ const (return ((), s))
  
getLabel :: (MonadLIO l m, Label l) => m l
getLabel = liftLIO $ gets $ view $ _1 . cur

getClearance :: (MonadLIO l m, Label l) => m l
getClearance = liftLIO $ gets $ view $ _1 . clearance

data Labeled l a = Labeled { _labeledLab :: l, _labeledVal :: a }
  deriving Generic

instance (Binary l, Binary a) => Binary (Labeled l a)

makeLenses ''Labeled

raise :: (SemiLattice l, MonadLIO l m, Label l, C l m) => String -> l -> m ()
raise msg l = do
  l' <- liftLIO $ gets $ view _1
  b <- view cur l' .⊔. l ⊑ view clearance l'
  unless b $
    fail ("IFC violation (" ++ msg ++ "): " ++
           show (view cur l') ++ " ⊔ " ++ show l  ++
           " ⊑ " ++ show (view clearance l'))
  liftLIO $ modify $ over (_1 . cur) (l .⊔.)
  
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

(∈) :: (MonadLIO l m, Label l, C l m) => l -> BoundedLabel l -> m Bool
(∈) l lab = do
  --liftLIO $ LIO $ lift $ putStrLn $ show (view cur lab) ++ " ⊑ " ++ show l
  x <- view cur lab ⊑ l
  if not x then return False
  else do
    --liftLIO $ LIO $ lift $ putStrLn $ show l ++ " ⊑ " ++ show (view clearance lab)  
    l ⊑ view clearance lab

label :: (MonadLIO l m, Label l, C l m, ToLabel c l) => c -> a -> m (Labeled l a)
label c x = do
  lab <- liftLIO $ gets $ view _1
  b <- l ∈ lab
  unless b $
    fail ("IFC violation (label): " ++
           show (view cur lab) ++
           " ⊑ " ++ show l ++
           " ⊑ " ++ show (view clearance lab))
  return $ Labeled {_labeledLab = l, _labeledVal = x }
  where l = (%) c
  
unlabel :: (MonadLIO l m, Label l, C l m) => Labeled l a -> m a
unlabel lab = do
  raise "unlabel" (labelOf lab)
  return (view labeledVal lab)

toLabeled :: forall l m c a . (MonadLIO l m, Label l, C l m, ToLabel c l) => c -> m a -> m (Labeled l a)
toLabeled c m = do
  l' <- liftLIO $ gets $ view _1
  res <- m
  l'' <- liftLIO $ gets $ view $ _1 . cur
  b <- l'' ⊑ c
  unless b $ do
    fail ("IFC violation (toLabeled): " ++ show l'' ++ " ⊑ " ++ show ((%) c :: l))
  liftLIO $ modify $ (_1 .~ l')
  label c res

toLabeled_ :: forall l m c a . (MonadLIO l m, Label l, C l m, ToLabel c l) => c -> m a -> m ()
toLabeled_ c m = do
  l' <- liftLIO $ gets $ view _1
  res <- m
  l'' <- liftLIO $ gets $ view $ _1 . cur
  b <- l'' ⊑ c
  unless b $ do
    fail ("IFC violation (toLabeled_): " ++ show l'' ++ " ⊑ " ++ show ((%) c :: l))
  liftLIO $ modify $ (_1 .~ l')

getStrategy :: (MonadLIO l m, Label l, C l m) => m (Strategy l)
getStrategy = liftLIO $ gets $ view _2

labelOf :: Labeled l a -> l
labelOf = view labeledLab

newtype LIORef l a = LIORef { unLIORef :: Labeled l (IORef a) }

newRef :: forall l m c a . (MonadLIO l m, Label l, C l m, ToLabel c l) => c -> a -> m (LIORef l a)
newRef c x = do
  lab <- liftLIO $ gets $ view _1
  b <- ((%) c) ∈ lab
  liftLIO . LIO . StateT $ \(lab, strat) -> do
  unless b $
    fail ("IFC violation (new): " ++
           show (view cur lab) ++
           " ⊑ " ++ show ((%) c :: l) ++
           " ⊑ " ++ show (view clearance lab))
  r <- newIORef x
  return (LIORef (Labeled {_labeledLab = (%) c, _labeledVal = r}), (lab, strat))

readRef :: (MonadLIO l m, Label l, C l m) => LIORef l a -> m a
readRef (LIORef lref) =
  raise "readRef" (labelOf lref) >> unlabel lref >>= \r -> do
  liftLIO . LIO . StateT $ \s -> do
    x <- readIORef r
    return (x, s)

(!) :: (MonadLIO l m, Label l, C l m) => LIORef l a -> m a
(!) = readRef

writeRef :: (MonadLIO l m, Label l, C l m) => LIORef l a -> a -> m ()
writeRef (LIORef lref) x = do
  lab <- liftLIO $ gets $ view _1
  b <- labelOf lref ∈ lab
  unless b $
    fail ("IFC violation (write): " ++
           show (view cur lab) ++
           " ⊑ " ++ show (labelOf lref) ++
           " ⊑ " ++ show (view clearance lab))
    
  unlabel lref >>= \ref ->
    liftLIO . LIO . StateT $ \s -> do
      writeIORef ref x
      return ((), s)

(.=) :: (MonadLIO l m, Label l, C l m) => LIORef l a -> a -> m ()
(.=) = writeRef

{- These weird instances are needed for networking -}
instance Label l => MonadThrow (LIO l) where
  throwM = LIO . throwM

instance Label l => MonadCatch (LIO l) where
  catch (LIO m) f = LIO $ catch m (unLIO . f)

instance Label l => MonadMask (LIO l) where
  mask a = LIO $ mask $ \u -> unLIO (a $ q u)
    where q u (LIO b) = LIO (u b)
    
  uninterruptibleMask a = LIO $ uninterruptibleMask $ \u -> unLIO (a $ q u)
    where q u (LIO b) = LIO (u b)

  generalBracket acquire release use = LIO $ generalBracket
    (unLIO acquire)
    (\resource exitCase -> unLIO (release resource exitCase))
    (\resource -> unLIO (use resource))

instance Label l => ForkableMonad (LIO l) where
  forkIO (LIO m) = LIO $ forkIO m

instance Label l => MonadFix (LIO l) where
  mfix f = LIO $ mfix $ \a -> unLIO (f a)
