{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Assertion.AssertionLanguage
  ( Arith(..)
  , ArithAlgebra(..)
  , Assertion(..)
  , AssertionAlgebra(..)
  , Name(..)
  , SubstitutableArith(..)
  , aAnd
  , aImp
  , aOr
  , eval
  , freeVars
  , subAriths
  , toSMT
  ) where

import Ceili.Evaluation
import Ceili.Literal
import Ceili.Name
import Ceili.ProgState
import Ceili.SMTString
import Data.ByteString ( ByteString )
import qualified Data.ByteString.Char8 as S8
import qualified Data.Map as Map
import Data.Set  ( Set )
import qualified Data.Set as Set
import Prettyprinter


----------------------------
-- Arithmetic Expressions --
----------------------------

data Arith t = Num t
             | Var Name
             | Add [Arith t]
             | Sub [Arith t]
             | Mul [Arith t]
             | Div (Arith t) (Arith t)
             | Mod (Arith t) (Arith t)
             | Pow (Arith t) (Arith t)
           deriving (Eq, Ord, Functor)

instance Pretty t => Show (Arith t) where
  show = show . pretty

bsToSexp :: SMTString a => ByteString -> [a] -> ByteString
bsToSexp name as = "(" <> name <> " "<> (S8.intercalate " " $ map toSMT as) <> ")"

instance MappableNames (Arith t) where
  mapNames f arith = case arith of
    Num x     -> Num x
    Var tname -> Var (mapNames f tname)
    Add as    -> Add $ map (mapNames f) as
    Sub as    -> Sub $ map (mapNames f) as
    Mul as    -> Mul $ map (mapNames f) as
    Div a1 a2 -> Div (mapNames f a1) (mapNames f a2)
    Mod a1 a2 -> Mod (mapNames f a1) (mapNames f a2)
    Pow a1 a2 -> Pow (mapNames f a1) (mapNames f a2)

instance CollectableNames (Arith t) where
  namesIn arith = case arith of
    Num _     -> Set.empty
    Var tname -> namesIn tname
    Add as    -> Set.unions $ map namesIn as
    Sub as    -> Set.unions $ map namesIn as
    Mul as    -> Set.unions $ map namesIn as
    Div a1 a2 -> Set.union (namesIn a1) (namesIn a2)
    Mod a1 a2 -> Set.union (namesIn a1) (namesIn a2)
    Pow a1 a2 -> Set.union (namesIn a1) (namesIn a2)

instance FreshableNames (Arith t) where
  freshen arith = case arith of
    Num i     -> return $ Num i
    Var tname -> return . Var =<< freshen tname
    Add as    -> return . Add =<< freshen as
    Sub as    -> return . Sub =<< freshen as
    Mul as    -> return . Mul =<< freshen as
    Div a1 a2 -> freshenBinop Div a1 a2
    Mod a1 a2 -> freshenBinop Mod a1 a2
    Pow a1 a2 -> freshenBinop Pow a1 a2

instance Ord t => CollectableLiterals (Arith t) t where
  litsIn arith = case arith of
    Num i     -> Set.singleton i
    Var _     -> Set.empty
    Add as    -> Set.unions $ map litsIn as
    Sub as    -> Set.unions $ map litsIn as
    Mul as    -> Set.unions $ map litsIn as
    Div a1 a2 -> Set.union (litsIn a1) (litsIn a2)
    Mod a1 a2 -> Set.union (litsIn a1) (litsIn a2)
    Pow a1 a2 -> Set.union (litsIn a1) (litsIn a2)

instance SMTString t => SMTString (Arith t) where
  toSMT arith = case arith of
    Num n     -> toSMT n
    Var name  -> toSMT name
    Add as    -> bsToSexp "+"   as
    Sub as    -> bsToSexp "-"   as
    Mul as    -> bsToSexp "*"   as
    Div a1 a2 -> bsToSexp "/"   [a1, a2]
    Mod a1 a2 -> bsToSexp "mod" [a1, a2]
    Pow a1 a2 -> bsToSexp "^"   [a1, a2]


----------------------
-- Arith Evaluation --
----------------------

class ArithAlgebra t where
  arZero :: t
  arOne  :: t
  arAdd  :: t -> t -> t
  arSub  :: t -> t -> t
  arMul  :: t -> t -> t
  arDiv  :: t -> t -> t
  arMod  :: t -> t -> t
  arExp  :: t -> t -> t

instance ArithAlgebra Integer where
  arZero = 0
  arOne  = 1
  arAdd  = (+)
  arSub  = (-)
  arMul  = (*)
  arDiv  = quot
  arMod  = mod
  arExp  = (^)

evalArith :: ArithAlgebra t => ProgState t -> Arith t -> t
evalArith state arith = case arith of
  Num i     -> i
  Var v     -> case Map.lookup v state of
                 Nothing -> arZero
                 Just n  -> n
  Add as    -> foldr arAdd arZero $ map (evalArith state) as
  Sub as    -> case as of
                 []      -> arZero
                 (a:as') -> foldl arSub (evalArith state a)
                            $ map (evalArith state) as'
  Mul as    -> foldr arMul arOne $ map (evalArith state) as
  Div a1 a2 -> arDiv (evalArith state a1) (evalArith state a2)
  Mod a1 a2 -> arMod (evalArith state a1) (evalArith state a2)
  Pow a1 a2 -> arExp (evalArith state a1) (evalArith state a2)

instance ArithAlgebra t => Evaluable c t (Arith t) t where
   eval _ = evalArith


----------------
-- Assertions --
----------------

data Assertion t = ATrue
                 | AFalse
                 | Atom     Name
                 | Not      (Assertion t)
                 | And      [Assertion t]
                 | Or       [Assertion t]
                 | Imp      (Assertion t) (Assertion t)
                 | Eq       (Arith t) (Arith t)
                 | Lt       (Arith t) (Arith t)
                 | Gt       (Arith t) (Arith t)
                 | Lte      (Arith t) (Arith t)
                 | Gte      (Arith t) (Arith t)
                 | Forall   [Name] (Assertion t)
                 | Exists   [Name] (Assertion t)
               deriving (Eq, Ord, Functor)

instance Pretty t => Show (Assertion t) where
  show = show . pretty

instance MappableNames (Assertion t) where
  mapNames f assertion = case assertion of
    ATrue       -> ATrue
    AFalse      -> AFalse
    Atom tname  -> Atom $ mapNames f tname
    Not a       -> Not  $ mapNames f a
    And as      -> And  $ map (mapNames f) as
    Or as       -> Or   $ map (mapNames f) as
    Imp a1 a2   -> Imp (mapNames f a1) (mapNames f a2)
    Eq a1 a2    -> Eq  (mapNames f a1) (mapNames f a2)
    Lt a1 a2    -> Lt  (mapNames f a1) (mapNames f a2)
    Gt a1 a2    -> Gt  (mapNames f a1) (mapNames f a2)
    Lte a1 a2   -> Lte (mapNames f a1) (mapNames f a2)
    Gte a1 a2   -> Gte (mapNames f a1) (mapNames f a2)
    Forall vs a -> Forall (map (mapNames f) vs) (mapNames f a)
    Exists vs a -> Exists (map (mapNames f) vs) (mapNames f a)

instance CollectableNames (Assertion t) where
  namesIn assertion = case assertion of
    ATrue       -> Set.empty
    AFalse      -> Set.empty
    Atom tname  -> namesIn tname
    Not a       -> namesIn a
    And as      -> Set.unions $ map namesIn as
    Or as       -> Set.unions $ map namesIn as
    Imp a1 a2   -> Set.union (namesIn a1) (namesIn a2)
    Eq a1 a2    -> Set.union (namesIn a1) (namesIn a2)
    Lt a1 a2    -> Set.union (namesIn a1) (namesIn a2)
    Gt a1 a2    -> Set.union (namesIn a1) (namesIn a2)
    Lte a1 a2   -> Set.union (namesIn a1) (namesIn a2)
    Gte a1 a2   -> Set.union (namesIn a1) (namesIn a2)
    Forall vs a -> Set.unions $ (namesIn a):(map namesIn vs)
    Exists vs a -> Set.unions $ (namesIn a):(map namesIn vs)

instance FreshableNames (Assertion t) where
  freshen assertion = case assertion of
    ATrue       -> return ATrue
    AFalse      -> return AFalse
    Atom tname  -> return . Atom =<< freshen tname
    Not a       -> return . Not =<< freshen a
    And as      -> return . And =<< freshen as
    Or as       -> return . Or =<< freshen as
    Imp a1 a2   -> freshenBinop Imp a1 a2
    Eq a1 a2    -> freshenBinop Eq a1 a2
    Lt a1 a2    -> freshenBinop Lt a1 a2
    Gt a1 a2    -> freshenBinop Gt a1 a2
    Lte a1 a2   -> freshenBinop Lte a1 a2
    Gte a1 a2   -> freshenBinop Gte a1 a2
    Forall vs a -> quant Forall vs a
    Exists vs a -> quant Exists vs a
    where
      quant op vs a = do
        vs' <- freshen vs
        a'  <- freshen a
        return $ op vs' a'

instance Ord t => CollectableLiterals (Assertion t) t where
  litsIn assertion = case assertion of
    ATrue      -> Set.empty
    AFalse     -> Set.empty
    Atom _     -> Set.empty
    Not a      -> litsIn a
    And as     -> Set.unions $ map litsIn as
    Or as      -> Set.unions $ map litsIn as
    Imp a1 a2  -> Set.union (litsIn a1) (litsIn a2)
    Eq a1 a2   -> Set.union (litsIn a1) (litsIn a2)
    Lt a1 a2   -> Set.union (litsIn a1) (litsIn a2)
    Gt a1 a2   -> Set.union (litsIn a1) (litsIn a2)
    Lte a1 a2  -> Set.union (litsIn a1) (litsIn a2)
    Gte a1 a2  -> Set.union (litsIn a1) (litsIn a2)
    Forall _ a -> litsIn a
    Exists _ a -> litsIn a

instance (SMTString t, SMTTypeString t) => SMTString (Assertion t) where
  toSMT assertion = case assertion of
    ATrue         -> "true"
    AFalse        -> "false"
    Atom name     -> toSMT name
    Not a         -> bsToSexp "not" [a]
    And as        -> bsToSexp "and" as
    Or as         -> bsToSexp "or" as
    Imp a1 a2     -> bsToSexp "=>" [a1, a2]
    Eq a1 a2      -> bsToSexp "="  [a1, a2]
    Lt a1 a2      -> bsToSexp "<"  [a1, a2]
    Gt a1 a2      -> bsToSexp ">"  [a1, a2]
    Lte a1 a2     -> bsToSexp "<=" [a1, a2]
    Gte a1 a2     -> bsToSexp ">=" [a1, a2]
    Forall vars a -> quantToSMT "forall" vars a
    Exists vars a -> quantToSMT "exists" vars a
    where
      quantToSMT :: (SMTString t, SMTTypeString t) => ByteString -> [Name] -> Assertion t -> ByteString
      quantToSMT name qvars body =
        let typeStr = smtTypeString @t
            typedQVar qvar = "(" <> toSMT qvar <> " " <> typeStr <> ")"
            qvarsSMT = S8.intercalate " " $ map typedQVar qvars
        in "(" <> name <> " (" <> qvarsSMT <> ") " <> toSMT body <> ")"

aAnd :: [Assertion t] -> Assertion t
aAnd elts = case buildAndElts elts of
  []        -> ATrue
  AFalse:[] -> AFalse
  single:[] -> single
  as        -> And as
  where
    buildAndElts :: [Assertion t] -> [Assertion t]
    buildAndElts es = case es of
      []              -> []
      (ATrue:rest)    -> buildAndElts rest
      (AFalse:_)      -> [AFalse]
      ((And as):rest) -> buildAndElts (as ++ rest)
      (a:as)          -> a : buildAndElts as

aOr :: [Assertion t] -> Assertion t
aOr elts = case buildOrElts elts of
  []        -> ATrue
  ATrue:[]  -> ATrue
  single:[] -> single
  as        -> Or as
  where
    buildOrElts :: [Assertion t] -> [Assertion t]
    buildOrElts es = case es of
      []             -> []
      (ATrue:_)      -> [ATrue]
      (AFalse:rest)  -> buildOrElts rest
      ((Or as):rest) -> buildOrElts (as ++ rest)
      (a:as)         -> a : buildOrElts as

aImp :: Assertion t -> Assertion t -> Assertion t
aImp p q = case (p, q) of
  (ATrue, _)  -> q
  (AFalse, _) -> ATrue
  (_, ATrue)  -> ATrue
  (_, AFalse) -> Not p
  _           -> Imp p q

--------------------------
-- Assertion Evaluation --
--------------------------

class AssertionAlgebra t where
  asEq  :: t -> t -> Bool
  asLt  :: t -> t -> Bool
  asGt  :: t -> t -> Bool
  asLte :: t -> t -> Bool
  asGte :: t -> t -> Bool

instance AssertionAlgebra Integer where
  asEq  = (==)
  asLt  = (<)
  asGt  = (>)
  asLte = (<=)
  asGte = (>=)

instance (ArithAlgebra t, AssertionAlgebra t) => Evaluable c t (Assertion t) Bool where
 eval ctx state assertion = case assertion of
   ATrue     -> True
   AFalse    -> False
   Atom _    -> False -- This assumes states cannot store booleans.
   Not a     -> not $ eval ctx state a
   And as    -> and $ map (eval ctx state) as
   Or  as    -> or  $ map (eval ctx state) as
   Imp a1 a2 -> (not $ eval ctx state a1) || (eval ctx state a2)
   Eq  a1 a2 -> asEq  (evalArith state a1) (evalArith state a2)
   Lt  a1 a2 -> asLt  (evalArith state a1) (evalArith state a2)
   Gt  a1 a2 -> asGt  (evalArith state a1) (evalArith state a2)
   Lte a1 a2 -> asLte (evalArith state a1) (evalArith state a2)
   Gte a1 a2 -> asGte (evalArith state a1) (evalArith state a2)
   Forall _ _ -> error "Quantified formula evaluation not supported."
   Exists _ _ -> error "Quantified formula evaluation not supported."


------------------------------
--- Arithmetic Substitution --
------------------------------

class SubstitutableArith t a where
  subArith :: Name -> (Arith t) -> a -> a

instance SubstitutableArith t (Arith t) where
  subArith from to arith =
    let sub = subArith from to
    in case arith of
      Num x     -> Num x
      Var name  -> if from == name then to else Var name
      Add as    -> Add $ map sub as
      Sub as    -> Sub $ map sub as
      Mul as    -> Mul $ map sub as
      Div a1 a2 -> Div (sub a1) (sub a2)
      Mod a1 a2 -> Mod (sub a1) (sub a2)
      Pow a1 a2 -> Pow (sub a1) (sub a2)

instance SubstitutableArith t (Assertion t) where
  subArith from to assertion =
    let sub = subArith from to
    in case assertion of
      ATrue         -> ATrue
      AFalse        -> AFalse
      Atom tname    -> Atom tname
      Not a         -> Not $ sub a
      And as        -> And $ map sub as
      Or as         -> Or  $ map sub as
      Imp a1 a2     -> Imp (sub a1) (sub a2)
      Eq a1 a2      -> Eq  (subArith from to a1) (subArith from to a2)
      Lt a1 a2      -> Lt  (subArith from to a1) (subArith from to a2)
      Gt a1 a2      -> Gt  (subArith from to a1) (subArith from to a2)
      Lte a1 a2     -> Lte (subArith from to a1) (subArith from to a2)
      Gte a1 a2     -> Gte (subArith from to a1) (subArith from to a2)
      Forall vars a -> Forall vars (sub a)
      Exists vars a -> Exists vars (sub a)

subAriths :: SubstitutableArith t a => [Name] -> [Arith t] -> a -> a
subAriths from to sa = foldr (uncurry subArith) sa $ zip from to


--------------------
-- Free Variables --
--------------------

class FreeVariables a where
  freeVars :: a -> Set Name

instance FreeVariables (Arith t) where
  freeVars arith = case arith of
    Num _     -> Set.empty
    Var ident -> Set.singleton ident
    Add as    -> Set.unions $ map freeVars as
    Sub as    -> Set.unions $ map freeVars as
    Mul as    -> Set.unions $ map freeVars as
    Div a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Mod a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Pow a1 a2 -> Set.union (freeVars a1) (freeVars a2)

instance FreeVariables (Assertion t) where
  freeVars assertion = case assertion of
    ATrue        -> Set.empty
    AFalse       -> Set.empty
    Atom i       -> Set.singleton i
    Not  a       -> freeVars a
    And  as      -> Set.unions $ map freeVars as
    Or   as      -> Set.unions $ map freeVars as
    Imp  a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Eq   a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Lt   a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Gt   a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Lte  a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Gte  a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Forall ids a -> Set.difference (freeVars a) (Set.fromList ids)
    Exists ids a -> Set.difference (freeVars a) (Set.fromList ids)


--------------------
-- Pretty Printer --
--------------------

toSexp :: Pretty a => Doc ann -> [a] -> Doc ann
toSexp name as = sexpEnclose $ name:(map pretty as)

sexpEnclose :: [Doc ann] -> Doc ann
sexpEnclose = encloseSep lparen rparen space

instance Pretty t => Pretty (Arith t) where
  pretty arith = case arith of
    Num n     -> pretty n
    Var name  -> pretty name
    Add as    -> toSexp "+"   as
    Sub as    -> toSexp "-"   as
    Mul as    -> toSexp "*"   as
    Div a1 a2 -> toSexp "/"   [a1, a2]
    Mod a1 a2 -> toSexp "mod" [a1, a2]
    Pow a1 a2 -> toSexp "^"   [a1, a2]


instance Pretty t => Pretty (Assertion t) where
  pretty assertion = case assertion of
    ATrue         -> "true"
    AFalse        -> "false"
    Atom name     -> pretty name
    Not a         -> toSexp "not" [a]
    And as        -> toSexp "and" as
    Or as         -> toSexp "or" as
    Imp a1 a2     -> toSexp "=>" [a1, a2]
    Eq a1 a2      -> toSexp "="  [a1, a2]
    Lt a1 a2      -> toSexp "<"  [a1, a2]
    Gt a1 a2      -> toSexp ">"  [a1, a2]
    Lte a1 a2     -> toSexp "<=" [a1, a2]
    Gte a1 a2     -> toSexp ">=" [a1, a2]
    Forall vars a -> quantToSexp "forall" vars a
    Exists vars a -> quantToSexp "exists" vars a
    where
      quantToSexp name vs a = sexpEnclose $ [ name
                                            , sexpEnclose $ map pretty vs
                                            , pretty a ]
