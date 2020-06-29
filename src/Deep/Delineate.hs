module Deep.Delineate where

import           Deep.Expr

internalize :: ExprRep a => Expr a -> a
internalize = eval
{-# NOINLINE internalize #-}

externalize :: ExprRep a => a -> Expr a
externalize = error "externalize"
{-# NOINLINE externalize #-}

unrep :: Expr a -> a
unrep = error "unrep called"
{-# NOINLINE unrep #-}

