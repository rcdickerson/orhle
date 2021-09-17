{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CValue
  ( CValue(..)
  ) where

import Ceili.Assertion
import Ceili.Assertion.AssertionParser ( integer )
import Ceili.Embedding
import Ceili.Language.AExp
import Ceili.SMTString
import Ceili.StatePredicate
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter

data CValue = Concrete Integer
            | WithChoice { cv_choiceVars  :: Set Name
                         , cv_constraints :: Set (Assertion Integer)
                         , cv_value       :: Arith Integer
                         }
            deriving (Eq, Ord, Show)

instance Pretty CValue where
  pretty (Concrete i) = pretty i
  pretty (WithChoice _ constraints val) = pretty val <> ", s.t. " <> (pretty $ Set.toList constraints)

instance SMTString CValue where
  toSMT (Concrete i) = toSMT i
  toSMT (WithChoice cvars constraints val) = toSMT val

instance SMTTypeString CValue where
  smtTypeString = smtTypeString @Integer

instance AssertionParseable CValue where
  parseLiteral = integer >>= return . Concrete


----------------
-- Operations --
----------------

instance Embeddable Integer CValue where embed = Concrete

cvalAdd :: CValue -> CValue -> CValue
cvalAdd = cvalBinop (+) (\l r -> Add [l, r])

cvalSub :: CValue -> CValue -> CValue
cvalSub = cvalBinop (-) (\l r -> Sub [l, r])

cvalMul :: CValue -> CValue -> CValue
cvalMul = cvalBinop (*) (\l r -> Mul [l, r])

cvalDiv :: CValue -> CValue -> CValue
cvalDiv = cvalBinop quot Div

cvalExp :: CValue -> CValue -> CValue
cvalExp = cvalBinop (^) Pow

cvalMod :: CValue -> CValue -> CValue
cvalMod = cvalBinop mod Mod

cvalBinop :: (Integer -> Integer -> Integer)
          -> (Arith Integer -> Arith Integer -> Arith Integer)
          -> CValue -> CValue -> CValue
cvalBinop fconc fabs lhs rhs = case (lhs, rhs) of
  (Concrete i, Concrete j) ->
    Concrete $ fconc i j
  (Concrete i, WithChoice cvars constraints val) ->
    WithChoice cvars constraints $ fabs (Num i) val
  (WithChoice cvars constraints val, Concrete j) ->
    WithChoice cvars constraints $ fabs val (Num j)
  (WithChoice lcvars lconstraints lval, WithChoice rcvars rconstraints rval) ->
    WithChoice (Set.union lcvars rcvars)
               (Set.union lconstraints rconstraints)
               (fabs lval rval)

instance AExpAlgebra CValue where
  aeZero = Concrete 0
  aeAdd  = cvalAdd
  aeSub  = cvalSub
  aeMul  = cvalMul
  aeDiv  = cvalDiv
  aeExp  = cvalExp
  aeMod  = cvalMod

instance ArithAlgebra CValue where
  arZero = Concrete 0
  arOne  = Concrete 1
  arAdd  = cvalAdd
  arSub  = cvalSub
  arMul  = cvalMul
  arDiv  = cvalDiv
  arExp  = cvalExp
  arMod  = cvalMod

instance StatePredicate (Assertion CValue) CValue where
  testState assertion state = eval () state assertion
