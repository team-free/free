{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Trans.Cofree
-- Copyright   :  (C) 2008-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- The cofree comonad transformer
----------------------------------------------------------------------------
module Control.Comonad.Trans.Cofree
  ( CofreeT(..)
  , cofree, runCofree
  , CofreeF(..)
  , ComonadCofree(..)
  , headF
  , tailF
  , coiterT
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Cofree.Class
import Control.Category
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable
import Data.Functor.Identity
import Data.Semigroup
import Data.Traversable
import Prelude hiding (id,(.))

#if defined(GHC_TYPEABLE) || __GLASGOW_HASKELL__ >= 707
import Data.Data
#endif

infixr 5 :<

-- | This is the base functor of the cofree comonad transformer.
data CofreeF f a b = a :< f b
  deriving (Eq,Ord,Show,Read
#if __GLASGOW_HASKELL__ >= 707
           ,Typeable
#endif
           )

-- | Extract the head of the base functor
headF :: CofreeF f a b -> a
headF (a :< _) = a

-- | Extract the tails of the base functor
tailF :: CofreeF f a b -> f b
tailF (_ :< as) = as

instance Functor f => Functor (CofreeF f a) where
  fmap f (a :< as)  = a :< fmap f as

instance Foldable f => Foldable (CofreeF f a) where
  foldMap f (_ :< as) = foldMap f as

instance Traversable f => Traversable (CofreeF f a) where
  traverse f (a :< as) = (a :<) <$> traverse f as

instance Functor f => Bifunctor (CofreeF f) where
  bimap f g (a :< as)  = f a :< fmap g as

instance Foldable f => Bifoldable (CofreeF f) where
  bifoldMap f g (a :< as)  = f a `mappend` foldMap g as

instance Traversable f => Bitraversable (CofreeF f) where
  bitraverse f g (a :< as) = (:<) <$> f a <*> traverse g as

  

-- | This is a cofree comonad of some functor @f@, with a comonad @w@ threaded through it at each level.
newtype CofreeT f w a = CofreeT { runCofreeT :: w (CofreeF f a (CofreeT f w a)) }

type Cofree f = CofreeT f Identity

cofree :: CofreeF f a (Cofree f a) -> Cofree f a
cofree = CofreeT . Identity
{-# INLINE cofree #-}

runCofree :: Cofree f a -> CofreeF f a (Cofree f a)
runCofree = runIdentity . runCofreeT
{-# INLINE runCofree #-}

instance (Functor f, Functor w) => Functor (CofreeT f w) where
  fmap f = CofreeT . fmap (bimap f (fmap f)) . runCofreeT

instance (Functor f, Comonad w) => Comonad (CofreeT f w) where
  extract = headF . extract . runCofreeT
  extend f = CofreeT . extend (\w -> f (CofreeT w) :< (extend f <$> tailF (extract w))) . runCofreeT

instance (Foldable f, Foldable w) => Foldable (CofreeT f w) where
  foldMap f = foldMap (bifoldMap f (foldMap f)) . runCofreeT

instance (Traversable f, Traversable w) => Traversable (CofreeT f w) where
  traverse f = fmap CofreeT . traverse (bitraverse f (traverse f)) . runCofreeT

instance Functor f => ComonadTrans (CofreeT f) where
  lower = fmap headF . runCofreeT

instance (Functor f, Comonad w) => ComonadCofree f (CofreeT f w) where
  unwrap = tailF . extract . runCofreeT

instance Show (w (CofreeF f a (CofreeT f w a))) => Show (CofreeT f w a) where
  showsPrec d w = showParen (d > 10) $
    showString "CofreeT " . showsPrec 11 w

instance Read (w (CofreeF f a (CofreeT f w a))) => Read (CofreeT f w a) where
  readsPrec d = readParen (d > 10) $ \r ->
     [(CofreeT w, t) | ("CofreeT", s) <- lex r, (w, t) <- readsPrec 11 s]

instance Eq (w (CofreeF f a (CofreeT f w a))) => Eq (CofreeT f w a) where
  CofreeT a == CofreeT b = a == b

instance Ord (w (CofreeF f a (CofreeT f w a))) => Ord (CofreeT f w a) where
  compare (CofreeT a) (CofreeT b) = compare a b

-- This definition is equivalent to that of the Cofree module if 'w' is
-- identity. The monad laws should be easy to derive from the monad laws
-- for w, and the proof of associativity for the 'Identity' case.
--
-- Left identity:
--
-- return x >>= f
-- ==
-- C (return (x :< empty)) >>= f
-- ==
-- C $ (return (x :< empty)) >>= (\a :< m ->
--                 unC (f a) >>= (\b :< n ->
--                 return $ b :< (n <|> fmap (>>= f) m)
--
-- == { Left identity for 'w' } ==
-- 
--             C $ unC (f x) >>= (\b :< n ->
--                 return $ b :< (n <|> fmap (>>= f) empty)
-- 
-- == { fmap over empty } ==
--
--             C $ unC (f x) >>= (\b :< n ->
--                 return $ b :< (n <|> fmap (>>= f) empty)
--
-- == { empty is identity for <|> } == 
--
--             C $ unC (f x) >>= (\b :< n ->
--                 return $ b :< n
  
-- == { η-reduction, right identity for w } ==
--
--             C $ unC (f x)
-- ==
-- f x
--
-- Right identity: (m >>= return) == m
--
-- (C wx) >>= return
-- ==
-- (C wx) >>= (\x -> C $ return $ (x :< empty))
-- ==
-- C $ wx >>= (\a :< m -> unC (C $ return $ a :< empty)
--        >>= (\b :< n -> return $ b :< (n <|> fmap (>>= return) m)
-- == { coinduction } ==
-- C $ wx >>= (\a :< m -> unC (C $ return $ a :< empty)
--        >>= (\b :< n -> return $ b :< (n <|> fmap id m)
-- == { fmap id == id } ==
-- C $                            wx >>= (\a :< m ->
--     unC (C $ return $ a :< empty) >>= (\b :< n ->
--                            return $ b :< (n <|> m)
-- == { unC . C == id, left identity for w }
-- C $ wx >>= (\a :< m ->
--     let b :< n = a :< empty in
--     return $ b :< (n <|> m)
-- ==
-- C $ wx >>= (\a :< m -> return $ a :< (empty <|> m))
-- == { empty is identity for <|> }
-- C $ wx >>= (\a :< m -> return $ a :< m))
-- == { right identity for w } ==
-- C wx
--
--
-- Associativity: (m >>= g >>= h == m >>= (\x -> g x >>= h))
--
-- (C wa  >>= g) >>= h
--
-- == {definition} ==
-- C $ do
--       unC (C wa >>= g) >>= \(c :< o) ->
--        unC $ h c       >>= \(d :< p) _>
--        return $ d :< (p <|> fmap (>>= h) o)
--
-- == {definition} ==
-- C $ do
--      (wa             >>=   \(a :< m) ->
--       unC (g a)        >>= \(b :< n) ->
--       return $ b :< (m <|> fmap (>>= g) n)
--                      ) >>= \(c :< o) ->
--        unC $ h c       >>= \(d :< p) _>
--        return $ d :< (p <|> fmap (>>= h) o)
--
-- == { associativity of 'w' } ==
--
-- C $ do
--                                    wa  >>= \(a :< m) ->
--                              unC (g a) >>= \(b :< n) ->
--  return $ b :< (m <|> fmap (>>= g) m)  >>= \(c :< o) ->
--                        unC $ h c       >>= \(d :< p) _>
--        return $ d :< (p <|> fmap (>>= h) o)
--
-- == { left identity } ==
-- C $ do
--                                    wa  >>= \(a :< m) ->
--                              unC (g a) >>= \(b :< n) ->
--                              unC (h b) >>= \(d :< p) _>
--        return $ d :< (p <|> fmap (>>= h) (n <|> fmap (>>= g) m))
--
-- == { fmap distributes over (<|>), <|> is associative } ==
--
-- C $ do
--             wa     >>= \(a :< m) ->
--      unC (g a)     >>= \(b :< n) ->
--      unC (h b)     >>= \(d :< p) 
--   return $ d :< (p <|> (fmap (>>= h) n) <|> fmap (>>= h) (fmap (>>= g)  m))
--
-- == { ∀f ∀g . fmap (f . g) == fmap f . fmap g } ==
-- C $ do
--             wa     >>= \(a :< m) ->
--      unC (g a)     >>= \(b :< n) ->
--      unC (h b)     >>= \(d :< p) 
--   return $ d :< (p <|> (fmap (>>= h) n) <|> fmap ((>>= h) . (>>= g))  m)
--
-- == { coinduction }
--  
-- C $ do
--             wa     >>= \(a :< m) ->
--      unC (g a)     >>= \(b :< n) ->
--      unC (h b)     >>= \(d :< p) 
--   return $ d :< (p <|> (fmap (>>= h) n) <|> fmap (>>= (\x -> g x >>= h)) m)
--
-- == { associativity of <|> } ==
--
-- c $ do
--             wa     >>= \(a :< m) ->
--      unC (g a)     >>= \(b :< n) ->
--      unC (h b)     >>= \(d :< p) 
--   return $ d :< ((p <|> fmap (>>=h) n) <|> fmap (>>= (\x -> g x >>= h)) m
--
-- == { associativity, right identity for monads } ==
-- c $ do
--             (wa    >>= \(a :< m) ->
--      unC (g a)     >>= \(b :< n) ->
--      unC (h b)     >>= \(d :< p) 
--      return (d :< (p <|> (fmap >>= h) n))) >>= \(c :< o) ->
--   return $ c :< (o <|> fmap (>>= (\x -> g x >>= h)) m
-- ==
-- C $ do
--        wa          >>= \(a :< m) ->
--   unC (g a >>= h)  >>= \(c :< o) ->
--   return $ c :< (o <|> fmap (>>= (\x -> g x >>= h)) m)
-- ==
-- (C wa) >>= (\x -> g x >>= h)
  
instance (Alternative f, Monad w) => Monad (CofreeT f w) where
  return = CofreeT . return . (:< empty)
  (CofreeT cx) >>= f = CofreeT $ do
    (a :< m) <- cx
    (b :< n) <- runCofreeT $ f a
    return $ b :< (n <|> fmap (>>= f) m)

-- TODO: To justify the Applicative constraint instead of a Monad w constraint,
-- it must be shown that the result is an applicative functor, even if 'w' is not
-- a monad.
instance (Alternative f, Applicative w) =>
         Applicative (CofreeT f w) where
  pure = CofreeT . pure . (:< empty)
  
  -- If w is also a monad, then (<*>) equals (`ap`)
  --
  -- The proof uses coinduction for the case “produce one, consume one”.
  --
  -- For simplicity, name "C" and "unC" for CofreeT and runCofreeT.
  -- 
  -- g = (\f -> (CofreeT wa) >>= (\a -> return $ f a))
  -- (<*> a) == (>>= g)
  --
  -- Prove that: wf `ap` wa   == wf <*> g
  --
  -- (C wf) `ap` (C wa)
  --
  -- == {definition} ==
  -- 
  -- (C wf) >>= (\f -> (C wa) >>= (\a -> f a))
  -- 
  -- == {definition} ==
  --
  --                                   wf >>= \(f :< t) ->
  --  unC (C wa >>= (\a -> return $ f a)) >>= \(b :< n) ->
  --                               return $ b :< (n <|> fmap (>>= g) t)
  --
  -- == {coinductive step} ==
  --
  --                                   wf >>= \(f :< t) ->
  --  unC (C wa >>= (\a -> return $ f a)) >>= \(b :< n) ->
  --                               return $ b :< (n <|> fmap (<*> C wa) t)
  -- == {definition of fmap for monads}
  --
  --
  --                                   wf >>= \(f :< t) ->
  --                  unC (fmap f (C wa)) >>= \(b :< n) ->
  --                               return $ b :< (n <|> fmap (<*> C wa) t)
  --
  -- == {definition of fmap for C} ==
  --
  --                                             wf >>= \(f :< t) ->
  --                     fmap (bimap f (fmap f)) wa >>= \(b :< n) ->
  --                               return $ b :< (n <|> fmap (<*> C wa) t)
  --       
  -- == {definition of fmap for monads} ==
  --
  --                                             wf >>= \(f :< t) ->
  --    (wa >>= (\a -> return (bimap f (fmap f) a)  >>= \(b :< n) ->
  --                               return $ b :< (n <|> fmap (<*> C wa) t)
  -- 
  -- == { associativity of monads } ==
  --
  --                                   wf >>= \(f :< t) ->
  --                                   wa >>= \a        ->
  --        (return (bimap f (fmap f a))) >>= \(b :< n) -> 
  --                           return $ b :< (n <|> fmap (<*> a) m)
  --
  -- == { Left identity of monads } ==
  --
  --                                   wf >>= \(f :< t) ->
  --                                   wa >>= \(a       ->
  --                           let b :< n = bimap f (fmap f a)) in
  --                           return $ b :< (n <|> fmap (<*> a) m))
  --
  -- == { Equivalence of (>>=) and (<*>) for monad w.
  -- 
  --                                          \(f :< t) ->
  --                                          \(a       ->
  --                           let b :< n = bimap f (fmap f a)) in
  --                           return $ b :< (n <|> fmap (<*> a) m)))
  --
  -- == { definition of (<*>) } ==
  -- 
  -- (Cofree wf) <*> (CofreeT wa)
  --
  (CofreeT wf) <*> aa@(CofreeT wa) = CofreeT $
    ( \(f :< t) -> 
      -- (b :< n) <- runCofreeT $ fmap f wa
      \(a)      ->  
      let (b :< n) = bimap f (fmap f) a in 
      b :< (n <|> fmap (<*> aa) t)) <$> wf <*> wa

-- | Unfold a @CofreeT@ comonad transformer from a coalgebra and an initial comonad.
coiterT :: (Functor f, Comonad w) => (w a -> f (w a)) -> w a -> CofreeT f w a
coiterT psi = CofreeT . (extend $ \w -> extract w :< fmap (coiterT psi) (psi w))

#if defined(GHC_TYPEABLE) && __GLASGOW_HASKELL__ < 707

instance Typeable1 f => Typeable2 (CofreeF f) where
  typeOf2 t = mkTyConApp cofreeFTyCon [typeOf1 (f t)] where
    f :: CofreeF f a b -> f a
    f = undefined

instance (Typeable1 f, Typeable1 w) => Typeable1 (CofreeT f w) where
  typeOf1 t = mkTyConApp cofreeTTyCon [typeOf1 (f t), typeOf1 (w t)] where
    f :: CofreeT f w a -> f a
    f = undefined
    w :: CofreeT f w a -> w a
    w = undefined

cofreeFTyCon, cofreeTTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
cofreeTTyCon = mkTyCon "Control.Comonad.Trans.Cofree.CofreeT"
cofreeFTyCon = mkTyCon "Control.Comonad.Trans.Cofree.CofreeF"
#else
cofreeTTyCon = mkTyCon3 "free" "Control.Comonad.Trans.Cofree" "CofreeT"
cofreeFTyCon = mkTyCon3 "free" "Control.Comonad.Trans.Cofree" "CofreeF"
#endif
{-# NOINLINE cofreeTTyCon #-}
{-# NOINLINE cofreeFTyCon #-}

instance
  ( Typeable1 f, Typeable a, Typeable b
  , Data a, Data (f b), Data b
  ) => Data (CofreeF f a b) where
    gfoldl f z (a :< as) = z (:<) `f` a `f` as
    toConstr _ = cofreeFConstr
    gunfold k z c = case constrIndex c of
        1 -> k (k (z (:<)))
        _ -> error "gunfold"
    dataTypeOf _ = cofreeFDataType
    dataCast1 f = gcast1 f

instance
  ( Typeable1 f, Typeable1 w, Typeable a
  , Data (w (CofreeF f a (CofreeT f w a)))
  , Data a
  ) => Data (CofreeT f w a) where
    gfoldl f z (CofreeT w) = z CofreeT `f` w
    toConstr _ = cofreeTConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z CofreeT)
        _ -> error "gunfold"
    dataTypeOf _ = cofreeTDataType
    dataCast1 f = gcast1 f

cofreeFConstr, cofreeTConstr :: Constr
cofreeFConstr = mkConstr cofreeFDataType ":<" [] Infix
cofreeTConstr = mkConstr cofreeTDataType "CofreeT" [] Prefix
{-# NOINLINE cofreeFConstr #-}
{-# NOINLINE cofreeTConstr #-}

cofreeFDataType, cofreeTDataType :: DataType
cofreeFDataType = mkDataType "Control.Comonad.Trans.Cofree.CofreeF" [cofreeFConstr]
cofreeTDataType = mkDataType "Control.Comonad.Trans.Cofree.CofreeT" [cofreeTConstr]
{-# NOINLINE cofreeFDataType #-}
{-# NOINLINE cofreeTDataType #-}
#endif

-- lowerF :: (Functor f, Comonad w) => CofreeT f w a -> f a
-- lowerF = fmap extract . unwrap
