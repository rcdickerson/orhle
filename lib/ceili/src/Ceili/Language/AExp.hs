{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.AExp
  ( AExp(..)
  , AExpAlgebra(..)
  , aexpToArith
  , eval
  ) where

import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.Evaluation
import Ceili.Name
import Ceili.Literal
import Ceili.SMTString
import Ceili.ProgState
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prettyprinter

data AExp t
  = ALit t
  | AVar Name
  | AAdd (AExp t) (AExp t)
  | ASub (AExp t) (AExp t)
  | AMul (AExp t) (AExp t)
  | ADiv (AExp t) (AExp t)
  | AMod (AExp t) (AExp t)
  | APow (AExp t) (AExp t)
  deriving (Eq, Ord, Show, Functor)

instance CollectableNames (AExp t) where
  namesIn aexp = case aexp of
    ALit _ -> Set.empty
    AVar v -> Set.singleton v
    AAdd lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    ASub lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    AMul lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    ADiv lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    AMod lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    APow lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)

instance MappableNames (AExp t) where
  mapNames f aexp = case aexp of
    ALit i       -> ALit i
    AVar v       -> AVar (f v)
    AAdd lhs rhs -> AAdd (mapNames f lhs) (mapNames f rhs)
    ASub lhs rhs -> ASub (mapNames f lhs) (mapNames f rhs)
    AMul lhs rhs -> AMul (mapNames f lhs) (mapNames f rhs)
    ADiv lhs rhs -> ADiv (mapNames f lhs) (mapNames f rhs)
    AMod lhs rhs -> AMod (mapNames f lhs) (mapNames f rhs)
    APow lhs rhs -> APow (mapNames f lhs) (mapNames f rhs)

instance FreshableNames (AExp t) where
  freshen aexp = case aexp of
    ALit i -> return $ ALit i
    AVar v -> return . AVar =<< freshen v
    AAdd lhs rhs -> freshenBinop AAdd lhs rhs
    ASub lhs rhs -> freshenBinop ASub lhs rhs
    AMul lhs rhs -> freshenBinop AMul lhs rhs
    ADiv lhs rhs -> freshenBinop ADiv lhs rhs
    AMod lhs rhs -> freshenBinop AMod lhs rhs
    APow lhs rhs -> freshenBinop APow lhs rhs

instance Ord t => CollectableLiterals (AExp t) t where
  litsIn aexp = case aexp of
    ALit i -> Set.singleton i
    AVar _ -> Set.empty
    AAdd lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    ASub lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    AMul lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    ADiv lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    AMod lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    APow lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)

aexpToArith :: AExp t -> A.Arith t
aexpToArith aexp = case aexp of
  ALit i           -> A.Num i
  AVar var         -> A.Var var
  AAdd aexp1 aexp2 -> A.Add [aexpToArith aexp1, aexpToArith aexp2]
  ASub aexp1 aexp2 -> A.Sub [aexpToArith aexp1, aexpToArith aexp2]
  AMul aexp1 aexp2 -> A.Mul [aexpToArith aexp1, aexpToArith aexp2]
  ADiv aexp1 aexp2 -> let
    dividend = aexpToArith aexp1
    divisor  = aexpToArith aexp2
    in A.Div dividend divisor
  AMod aexp1 aexp2 -> let
    dividend = aexpToArith aexp1
    divisor  = aexpToArith aexp2
    in A.Mod dividend divisor
  APow aexp1 aexp2 -> let
    base  = aexpToArith aexp1
    power = aexpToArith aexp2
    in A.Pow base power


----------------
-- Evaluation --
----------------

class AExpAlgebra t where
  aeZero :: t
  aeAdd  :: t -> t -> t
  aeSub  :: t -> t -> t
  aeMul  :: t -> t -> t
  aeDiv  :: t -> t -> t
  aeExp  :: t -> t -> t
  aeMod  :: t -> t -> t

instance {-# OVERLAPPABLE #-} AExpAlgebra Integer where
  aeZero = 0
  aeAdd  = (+)
  aeSub  = (-)
  aeMul  = (*)
  aeDiv  = quot
  aeExp  = (^)
  aeMod  = mod

instance AExpAlgebra t => Evaluable c t (AExp t) t where
  eval ctx st aexp = case aexp of
    ALit i       -> i
    AVar v       -> Map.findWithDefault (aeZero @t) v st
    AAdd lhs rhs -> aeAdd (eval ctx st lhs) (eval ctx st rhs)
    ASub lhs rhs -> aeSub (eval ctx st lhs) (eval ctx st rhs)
    AMul lhs rhs -> aeMul (eval ctx st lhs) (eval ctx st rhs)
    ADiv lhs rhs -> aeDiv (eval ctx st lhs) (eval ctx st rhs)
    AMod lhs rhs -> aeMod (eval ctx st lhs) (eval ctx st rhs)
    APow lhs rhs -> aeExp (eval ctx st lhs) (eval ctx st rhs)


--------------------
-- Pretty Printer --
--------------------

instance Pretty t => Pretty (AExp t) where
  pretty aexp =
    case aexp of
      ALit i -> pretty i
      AVar name -> pretty $ showSMT name
      AAdd lhs rhs -> maybeParens lhs <+> "+" <+> maybeParens rhs
      ASub lhs rhs -> maybeParens lhs <+> "-" <+> maybeParens rhs
      AMul lhs rhs -> maybeParens lhs <+> "*" <+> maybeParens rhs
      ADiv lhs rhs -> maybeParens lhs <+> "/" <+> maybeParens rhs
      AMod lhs rhs -> maybeParens lhs <+> "%" <+> maybeParens rhs
      APow lhs rhs -> maybeParens lhs <+> "^" <+> maybeParens rhs

maybeParens :: Pretty t => (AExp t) -> Doc ann
maybeParens aexp =
  case aexp of
    ALit _ -> pretty aexp
    AVar _ -> pretty aexp
    _      -> parens $ pretty aexp
