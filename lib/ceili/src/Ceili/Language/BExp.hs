{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.BExp
  ( AExpAlgebra(..)
  , BExp(..)
  , BExpAlgebra(..)
  , bexpToAssertion
  , eval
  ) where

import Ceili.Assertion.AssertionLanguage ( Assertion)
import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.Language.AExp ( AExp(..), AExpAlgebra(..), aexpToArith )
import Ceili.Evaluation
import Ceili.Name
import Ceili.Literal
import Ceili.ProgState
import qualified Data.Set as Set
import Prettyprinter


-------------------------
-- Boolean Expressions --
-------------------------

data BExp t
  = BTrue
  | BFalse
  | BNot (BExp t)
  | BAnd (BExp t) (BExp t)
  | BOr  (BExp t) (BExp t)
  | BEq  (AExp t) (AExp t)
  | BNe  (AExp t) (AExp t)
  | BLe  (AExp t) (AExp t)
  | BGe  (AExp t) (AExp t)
  | BLt  (AExp t) (AExp t)
  | BGt  (AExp t) (AExp t)
  deriving (Eq, Ord, Show, Functor)

instance CollectableNames (BExp t) where
  namesIn bexp = case bexp of
    BTrue        -> Set.empty
    BFalse       -> Set.empty
    BNot b       -> namesIn b
    BAnd b1  b2  -> Set.union (namesIn b1)  (namesIn b2)
    BOr  b1  b2  -> Set.union (namesIn b1)  (namesIn b2)
    BEq  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BNe  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BLe  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BGe  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BLt  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BGt  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)

instance MappableNames (BExp t) where
  mapNames _ BTrue        = BTrue
  mapNames _ BFalse       = BFalse
  mapNames f (BNot b)     = BNot $ mapNames f b
  mapNames f (BAnd b1 b2) = BAnd (mapNames f b1) (mapNames f b2)
  mapNames f (BOr b1 b2)  = BOr (mapNames f b1) (mapNames f b2)
  mapNames f (BEq a1 a2)  = BEq (mapNames f a1) (mapNames f a2)
  mapNames f (BNe a1 a2)  = BNe (mapNames f a1) (mapNames f a2)
  mapNames f (BLe a1 a2)  = BLe (mapNames f a1) (mapNames f a2)
  mapNames f (BGe a1 a2)  = BGe (mapNames f a1) (mapNames f a2)
  mapNames f (BLt a1 a2)  = BLt (mapNames f a1) (mapNames f a2)
  mapNames f (BGt a1 a2)  = BGt (mapNames f a1) (mapNames f a2)

instance FreshableNames (BExp t) where
  freshen bexp = case bexp of
    BTrue  -> return BTrue
    BFalse -> return BFalse
    BNot b -> return . BNot =<< freshen b
    BAnd b1 b2 -> freshenBinop BAnd b1 b2
    BOr  b1 b2 -> freshenBinop BOr  b1 b2
    BEq  a1 a2 -> freshenBinop BEq  a1 a2
    BNe  a1 a2 -> freshenBinop BNe  a1 a2
    BLe  a1 a2 -> freshenBinop BLe  a1 a2
    BGe  a1 a2 -> freshenBinop BGe  a1 a2
    BLt  a1 a2 -> freshenBinop BLt  a1 a2
    BGt  a1 a2 -> freshenBinop BGt  a1 a2

instance Ord t => CollectableLiterals (BExp t) t where
  litsIn bexp = case bexp of
    BTrue        -> Set.empty
    BFalse       -> Set.empty
    BNot b       -> litsIn b
    BAnd b1  b2  -> Set.union (litsIn b1)  (litsIn b2)
    BOr  b1  b2  -> Set.union (litsIn b1)  (litsIn b2)
    BEq  lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    BNe  lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    BLe  lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    BGe  lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    BLt  lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    BGt  lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)

bexpToAssertion :: BExp t -> Assertion t
bexpToAssertion bexp = case bexp of
  BTrue      -> A.ATrue
  BFalse     -> A.AFalse
  BNot b     -> A.Not $ bexpToAssertion b
  BAnd b1 b2 -> A.And [bexpToAssertion b1, bexpToAssertion b2]
  BOr  b1 b2 -> A.Or  [bexpToAssertion b1, bexpToAssertion b2]
  BEq  a1 a2 -> A.Eq  (aexpToArith a1) (aexpToArith a2)
  BNe  a1 a2 -> A.Not $ A.Eq (aexpToArith a1) (aexpToArith a2)
  BLe  a1 a2 -> A.Lte (aexpToArith a1) (aexpToArith a2)
  BGe  a1 a2 -> A.Gte (aexpToArith a1) (aexpToArith a2)
  BGt  a1 a2 -> A.Gt  (aexpToArith a1) (aexpToArith a2)
  BLt  a1 a2 -> A.Lt  (aexpToArith a1) (aexpToArith a2)


----------------
-- Evaluation --
----------------

class BExpAlgebra t where
  beEq  :: t -> t -> Bool
  beLt  :: t -> t -> Bool
  beGt  :: t -> t -> Bool
  beLte :: t -> t -> Bool
  beGte :: t -> t -> Bool

instance BExpAlgebra Integer where
  beEq  = (==)
  beLt  = (<)
  beGt  = (>)
  beLte = (<=)
  beGte = (>=)

instance ( AExpAlgebra t
         , BExpAlgebra t
         ) => Evaluable c t (BExp t) Bool where
  eval ctx st bexp = case bexp of
    BTrue      -> True
    BFalse     -> False
    BNot b     -> not $ eval ctx st b
    BAnd b1 b2 -> (eval ctx st b1) && (eval ctx st b2)
    BOr  b1 b2 -> (eval ctx st b1) || (eval ctx st b2)
    BEq  a1 a2 -> beEq (evalAExp ctx st a1) (evalAExp ctx st a2)
    BNe  a1 a2 -> not $ beEq (evalAExp ctx st a1) (evalAExp ctx st a2)
    BLe  a1 a2 -> beLte (evalAExp ctx st a1) (evalAExp ctx st a2)
    BGe  a1 a2 -> beGte (evalAExp ctx st a1) (evalAExp ctx st a2)
    BGt  a1 a2 -> beGt  (evalAExp ctx st a1) (evalAExp ctx st a2)
    BLt  a1 a2 -> beLt  (evalAExp ctx st a1) (evalAExp ctx st a2)
    where
      evalAExp :: AExpAlgebra t => c -> ProgState t -> AExp t -> t
      evalAExp = eval


--------------------
-- Pretty Printer --
--------------------

instance Pretty t => Pretty (BExp t) where
  pretty bexp =
    case bexp of
      BTrue      -> "true"
      BFalse     -> "false"
      BNot b     -> "!" <> maybeParens b
      BAnd b1 b2 -> pretty b1 <+> "&&" <+> pretty b2
      BOr  b1 b2 -> pretty b1 <+> "||" <+> pretty b2
      BEq  b1 b2 -> pretty b1 <+> "==" <+> pretty b2
      BNe  b1 b2 -> pretty b1 <+> "!=" <+> pretty b2
      BLe  b1 b2 -> pretty b1 <+> "<=" <+> pretty b2
      BGe  b1 b2 -> pretty b1 <+> ">=" <+> pretty b2
      BGt  b1 b2 -> pretty b1 <+> ">"  <+> pretty b2
      BLt  b1 b2 -> pretty b1 <+> "<"  <+> pretty b2

maybeParens :: Pretty t => (BExp t) -> Doc ann
maybeParens bexp =
  case bexp of
    BTrue  -> pretty bexp
    BFalse -> pretty bexp
    _      -> parens $ pretty bexp
