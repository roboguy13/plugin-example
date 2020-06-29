{-# LANGUAGE DeriveGeneric #-}

{-# OPTIONS_GHC -fexpose-all-unfoldings -dcore-lint -dsuppress-all -dno-suppress-type-applications -fprint-equality-relations -fplugin=Plugin.MatchPlugin #-}

module Test.Main where

import           GHC.Generics

import           Deep.Expr
import           Deep.Delineate

import           Data.Complex

default (Double)

instance ExprRep a => ExprRep (Complex a)

testTriple :: Double -> (Complex Double, Complex Double, Complex Double)
testTriple _ = (3.0 :+ 0, 2.0 :+ 0, 1.0 :+ 0)

test :: Complex Double
test =
  internalize (externalize
    (case testTriple 0 of
       (x, y, re :+ im) ->
          im :+ 0
    ))
{-# NOINLINE test #-}

main :: IO ()
main = print test

