module Ceili.Assertion
  ( Arith(..)
  , ArithAlgebra(..)
  , Assertion(..)
  , AssertionAlgebra(..)
  , AssertionParseable(..)
  , Name(..)
  , ParseError
  , SubstitutableArith(..)
  , aAnd
  , aImp
  , aOr
  , assertionAtState
  , freeVars
  , hasQuantifiers
  , parseArith
  , parseAssertion
  , subAriths
  , toSMT
  ) where

import Ceili.Assertion.AssertionLanguage
import Ceili.Assertion.AssertionParser
import Ceili.ProgState
import qualified Data.Map as Map

assertionAtState :: ProgState t -> Assertion t -> Assertion t
assertionAtState st assertion = Map.foldrWithKey subArith assertion arithSt
  where arithSt = Map.map Num st

hasQuantifiers :: Assertion t -> Bool
hasQuantifiers assertion = case assertion of
  ATrue      -> False
  AFalse     -> False
  Atom _     -> False
  Not a      -> hasQuantifiers a
  And as     -> or $ map hasQuantifiers as
  Or as      -> or $ map hasQuantifiers as
  Imp a1 a2  -> (hasQuantifiers a1) || (hasQuantifiers a2)
  Eq _ _     -> False
  Lt _ _     -> False
  Gt _ _     -> False
  Lte _ _    -> False
  Gte _ _    -> False
  Forall _ _ -> True
  Exists _ _ -> True
