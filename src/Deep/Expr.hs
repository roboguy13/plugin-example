{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

module Deep.Expr where

import           GHC.Generics
import           Data.Typeable
import           Data.Void

data ProdMatch a b = MkProdMatch { runProdMatch :: a -> b }

data Expr t where
  Lit :: Double -> Expr Double

  -- The constraints on this constructor seem to be necessary to avoid
  -- an out-of-scope type variable error in the plugin transformation:
  PairExp :: forall a b. (ExprRep a, ExprRep b) => Expr a -> Expr b -> Expr (a, b)

  CaseExp :: forall t x r. (ExprRep t, ExprRepTy x ~ x, ExprRepTy t ~ x) => Expr t -> Expr (ProdMatch x r) -> Expr r

  ProdMatchExp :: forall a b r.
    (ExprRep a, ExprRep b)
      => Expr (a -> ProdMatch b r) -> Expr (ProdMatch (a, b) r)

  OneProdMatch :: forall a b.
    (ExprRep a)
      => Expr (a -> b) -> Expr (ProdMatch a b)

  NullaryMatch :: forall a r.
    ExprRep a
      => Expr r -> Expr (ProdMatch a r)

  Add :: Expr Double -> Expr Double -> Expr Double

  Lam :: (ExprRep a) => (Expr a -> Expr b) -> Expr (a -> b)
  App :: Expr (a -> b) -> Expr a -> Expr b

  ConstructRep ::
    forall a. (Typeable a, ExprRep a) => Expr (ExprRepTy a) -> Expr a

evalProd :: Expr (ProdMatch s t) -> s -> t
evalProd (ProdMatchExp f) =
  \pair ->
    case pair of
      (x, y) -> runProdMatch (eval f x) y
evalProd (OneProdMatch f) = \x -> eval f x
evalProd (NullaryMatch x) = \_ -> eval x

eval :: forall a. Expr a -> a
eval (Lit x) = x
eval (PairExp x y) = (eval x, eval y)
eval (CaseExp s p) = evalProd p (repTy (eval s))
eval (Add x y) = eval x + eval y
eval (Lam f) = eval . f . rep
eval (App f x) = eval f (eval x)
eval (ConstructRep x) = unrepTy $ eval x
eval expr@(ProdMatchExp {}) = MkProdMatch (evalProd expr)
eval expr@(OneProdMatch {}) = MkProdMatch (evalProd expr)
eval (NullaryMatch x) = MkProdMatch (const (eval x))

class Typeable a => ExprRep a where
  type ExprRepTy a
  type ExprRepTy a = ExprRepTy (Rep a Void)

  rep :: a -> Expr a
  construct :: a -> Expr (ExprRepTy a)
  unrepTy :: ExprRepTy a -> a
  repTy :: a -> ExprRepTy a

  default rep :: (ExprRep (ExprRepTy a)) => a -> Expr a
  rep x = ConstructRep (construct x)
  {-# INLINABLE rep #-}


  default unrepTy :: (Generic a, ExprRepTy a ~ ExprRepTy (Rep a Void), ExprRep (Rep a Void))
    => ExprRepTy a -> a
  unrepTy x = (to :: Rep a Void -> a) (unrepTy x)
  {-# INLINABLE unrepTy #-}


  default construct :: (Generic a, ExprRep (Rep a Void), ExprRep (ExprRepTy a), ExprRepTy (Rep a Void) ~ ExprRepTy a) => a -> Expr (ExprRepTy a)
  construct x = construct ((from :: a -> Rep a Void) x)
  {-# INLINABLE construct #-}


  default repTy :: (Generic a, ExprRepTy a ~ ExprRepTy (Rep a Void), ExprRep (Rep a Void))
    => a -> ExprRepTy a
  repTy x = repTy ((from :: a -> Rep a Void) x)
  {-# INLINABLE repTy #-}


instance ExprRep Double where
  type ExprRepTy Double = Double
  construct = Lit
  rep = Lit
  unrepTy = id
  repTy = id

instance (ExprRep a, ExprRep b) => ExprRep (a, b) where
  type ExprRepTy (a, b) = (a, b)
  construct (a, b) = PairExp (rep a) (rep b)
  rep (a, b) = PairExp (rep a) (rep b)
  unrepTy = id
  repTy = id

instance (ExprRep a, ExprRep b, ExprRep c) => ExprRep (a, b, c)

---- Generics instances ----
instance (Typeable (M1 i c f p), ExprRep (f p), ExprRep (ExprRepTy (f p))) => ExprRep (M1 i c f p) where
  type ExprRepTy (M1 i c f p) = ExprRepTy (f p)

  construct = construct . unM1
  unrepTy = M1 . unrepTy
  repTy (M1 x) = repTy x

instance (Typeable ((p :*: q) x), ExprRep (p x), ExprRep (q x), ExprRep (ExprRepTy (p x)), ExprRep (ExprRepTy (q x))) => ExprRep ((p :*: q) x) where
  type ExprRepTy ((p :*: q) x) = (ExprRepTy (p x), ExprRepTy (q x))

  construct (x :*: y) = PairExp (construct x) (construct y)
  unrepTy (x, y) = unrepTy x :*: unrepTy y
  repTy (x :*: y) = (repTy x, repTy y)

instance (Typeable (K1 i c p), ExprRep c) => ExprRep (K1 i c p) where
  type ExprRepTy (K1 i c p) = c

  construct = rep . unK1
  unrepTy = K1
  repTy = unK1

