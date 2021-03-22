module Orhle.Assertion.AssertionLanguage
  ( Arith(..)
  , Assertion(..)
  , Ident(..)
  , Name(..)
  , Sort(..)
  , fillHole
  , freeVars
  , subArith
  ) where

import           Data.List ( intercalate )
import           Data.Set  ( Set )
import qualified Data.Set as Set
import           Orhle.Names ( Name(..)
                             , CollectableNames(..)
                             , MappableNames(..) )

-----------------
-- Identifiers --
-----------------

data Sort = Bool
          | Int
          deriving (Eq, Ord)

data Ident = Ident { identName :: Name
                   , identSort :: Sort
                   }
           deriving (Eq, Ord)

instance Show Sort where
  show Bool = "bool"
  show Int  = "int"

instance Show Ident where
  show (Ident name sort) = "(" ++ (show name) ++ " " ++ (show sort) ++ ")"

instance CollectableNames Ident where
  namesIn (Ident name _) = Set.singleton name

instance MappableNames Ident where
  mapNames f (Ident name sort) = Ident (f name) sort


----------------------------
-- Arithmetic Expressions --
----------------------------

data Arith = Num Integer
           | Var Ident
           | Add [Arith]
           | Sub [Arith]
           | Mul [Arith]
           | Div Arith Arith
           | Mod Arith Arith
           | Pow Arith Arith
           deriving (Eq, Ord)

showSexp :: Show a => String -> [a] -> String
showSexp name as = "(" ++ name ++ " " ++ (intercalate " " $ map show as) ++ ")"

instance Show Arith where
  show (Num n)     = show n
  show (Var ident) = show $ identName ident
  show (Add as)    = showSexp "+"   as
  show (Sub as)    = showSexp "-"   as
  show (Mul as)    = showSexp "*"   as
  show (Div a1 a2) = showSexp "/"   [a1, a2]
  show (Mod a1 a2) = showSexp "mod" [a1, a2]
  show (Pow a1 a2) = showSexp "^"   [a1, a2]

instance MappableNames Arith where
  mapNames _ (Num x)     = Num x
  mapNames f (Var ident) = Var (mapNames f ident)
  mapNames f (Add as)    = Add $ map (mapNames f) as
  mapNames f (Sub as)    = Sub $ map (mapNames f) as
  mapNames f (Mul as)    = Mul $ map (mapNames f) as
  mapNames f (Div a1 a2) = Div (mapNames f a1) (mapNames f a2)
  mapNames f (Mod a1 a2) = Mod (mapNames f a1) (mapNames f a2)
  mapNames f (Pow a1 a2) = Pow (mapNames f a1) (mapNames f a2)

instance CollectableNames Arith where
  namesIn (Num _)     = Set.empty
  namesIn (Var ident) = namesIn ident
  namesIn (Add as)    = Set.unions $ map namesIn as
  namesIn (Sub as)    = Set.unions $ map namesIn as
  namesIn (Mul as)    = Set.unions $ map namesIn as
  namesIn (Div a1 a2) = Set.union (namesIn a1) (namesIn a2)
  namesIn (Mod a1 a2) = Set.union (namesIn a1) (namesIn a2)
  namesIn (Pow a1 a2) = Set.union (namesIn a1) (namesIn a2)


----------------
-- Assertions --
----------------

data Assertion = ATrue
               | AFalse
               | Atom   Ident
               | Not    Assertion
               | And    [Assertion]
               | Or     [Assertion]
               | Imp    Assertion Assertion
               | Eq     Arith Arith
               | Lt     Arith Arith
               | Gt     Arith Arith
               | Lte    Arith Arith
               | Gte    Arith Arith
               | Forall [Ident] Assertion
               | Exists [Ident] Assertion
               | Hole   Int
               deriving (Eq, Ord)

showQuant :: Show a => String -> [Ident] -> a -> String
showQuant name qvars body = "(" ++ name ++ " "
                                ++ "(" ++ (intercalate " " $ map show qvars) ++ ")"
                                ++ (show body) ++ ")"

instance Show Assertion where
  show ATrue           = "true"
  show AFalse          = "false"
  show (Atom ident)    = show $ identName ident
  show (Not a)         = showSexp "not" [a]
  show (And as)        = showSexp "and" as
  show (Or as)         = showSexp "or" as
  show (Imp a1 a2)     = showSexp "=>" [a1, a2]
  show (Eq a1 a2)      = showSexp "="  [a1, a2]
  show (Lt a1 a2)      = showSexp "<"  [a1, a2]
  show (Gt a1 a2)      = showSexp ">"  [a1, a2]
  show (Lte a1 a2)     = showSexp "<=" [a1, a2]
  show (Gte a1 a2)     = showSexp ">=" [a1, a2]
  show (Forall vars a) = showQuant "forall" vars a
  show (Exists vars a) = showQuant "exists" vars a
  show (Hole i)        = "??" ++ (show i)

instance MappableNames Assertion where
  mapNames _ ATrue         = ATrue
  mapNames _ AFalse        = AFalse
  mapNames f (Atom ident)  = Atom $ mapNames f ident
  mapNames f (Not a)       = Not  $ mapNames f a
  mapNames f (And as)      = And  $ map (mapNames f) as
  mapNames f (Or as)       = Or   $ map (mapNames f) as
  mapNames f (Imp a1 a2)   = Imp (mapNames f a1) (mapNames f a2)
  mapNames f (Eq a1 a2)    = Eq  (mapNames f a1) (mapNames f a2)
  mapNames f (Lt a1 a2)    = Lt  (mapNames f a1) (mapNames f a2)
  mapNames f (Gt a1 a2)    = Gt  (mapNames f a1) (mapNames f a2)
  mapNames f (Lte a1 a2)   = Lte (mapNames f a1) (mapNames f a2)
  mapNames f (Gte a1 a2)   = Gte (mapNames f a1) (mapNames f a2)
  mapNames f (Forall vs a) = Forall (map (mapNames f) vs) (mapNames f a)
  mapNames f (Exists vs a) = Exists (map (mapNames f) vs) (mapNames f a)
  mapNames _ (Hole i)      = Hole i

instance CollectableNames Assertion where
  namesIn ATrue         = Set.empty
  namesIn AFalse        = Set.empty
  namesIn (Atom ident)  = namesIn ident
  namesIn (Not a)       = namesIn a
  namesIn (And as)      = Set.unions $ map namesIn as
  namesIn (Or as)       = Set.unions $ map namesIn as
  namesIn (Imp a1 a2)   = Set.union (namesIn a1) (namesIn a2)
  namesIn (Eq a1 a2)    = Set.union (namesIn a1) (namesIn a2)
  namesIn (Lt a1 a2)    = Set.union (namesIn a1) (namesIn a2)
  namesIn (Gt a1 a2)    = Set.union (namesIn a1) (namesIn a2)
  namesIn (Lte a1 a2)   = Set.union (namesIn a1) (namesIn a2)
  namesIn (Gte a1 a2)   = Set.union (namesIn a1) (namesIn a2)
  namesIn (Forall vs a) = Set.union (Set.fromList $ map identName vs) (namesIn a)
  namesIn (Exists vs a) = Set.union (Set.fromList $ map identName vs) (namesIn a)
  namesIn (Hole _)      = Set.empty

fillHole :: Int -> Assertion -> Assertion -> Assertion
fillHole holeId fill assertion = let
  fillRec = fillHole holeId fill
  in case assertion of
    ATrue      -> ATrue
    AFalse     -> AFalse
    Atom i     -> Atom i
    Not a      -> Not $ fillRec a
    And as     -> And $ map fillRec as
    Or  as     -> Or  $ map fillRec as
    Imp a1 a2  -> Imp (fillRec a1) (fillRec a2)
    Eq  a1 a2  -> Eq  a1 a2
    Lt  a1 a2  -> Lt  a1 a2
    Gt  a1 a2  -> Gt  a1 a2
    Lte a1 a2  -> Lte a1 a2
    Gte a1 a2  -> Gte a1 a2
    Forall v a -> Forall v (fillRec a)
    Exists v a -> Exists v (fillRec a)
    Hole i     -> if i == holeId then fill else (Hole i)


-----------------------------
-- Arithmetic Substitution --
-----------------------------

class SubstitutableArith a where
  subArith :: Ident -> Arith -> a -> a

instance SubstitutableArith Arith where
  subArith from to arith =
    let sub = subArith from to
    in case arith of
      Num x     -> Num x
      Var ident -> if from == ident then to else Var ident
      Add as    -> Add $ map sub as
      Sub as    -> Sub $ map sub as
      Mul as    -> Mul $ map sub as
      Div a1 a2 -> Div (sub a1) (sub a2)
      Mod a1 a2 -> Mod (sub a1) (sub a2)
      Pow a1 a2 -> Pow (sub a1) (sub a2)

instance SubstitutableArith Assertion where
  subArith from to assertion =
    let sub = subArith from to
    in case assertion of
      ATrue           -> ATrue
      AFalse          -> AFalse
      (Atom ident)    -> Atom ident
      (Not a)         -> Not $ sub a
      (And as)        -> And $ map sub as
      (Or as)         -> Or  $ map sub as
      (Imp a1 a2)     -> Imp (sub a1) (sub a2)
      (Eq a1 a2)      -> Eq  (subArith from to a1) (subArith from to a2)
      (Lt a1 a2)      -> Lt  (subArith from to a1) (subArith from to a2)
      (Gt a1 a2)      -> Gt  (subArith from to a1) (subArith from to a2)
      (Lte a1 a2)     -> Lte (subArith from to a1) (subArith from to a2)
      (Gte a1 a2)     -> Gte (subArith from to a1) (subArith from to a2)
      (Forall vars a) -> Forall vars (sub a)
      (Exists vars a) -> Exists vars (sub a)
      (Hole i)        -> Hole i


--------------------
-- Free Variables --
--------------------

class FreeVariables a where
  freeVars :: a -> Set Ident

instance FreeVariables Arith where
  freeVars arith = case arith of
    Num _     -> Set.empty
    Var ident -> Set.singleton ident
    Add as    -> Set.unions $ map freeVars as
    Sub as    -> Set.unions $ map freeVars as
    Mul as    -> Set.unions $ map freeVars as
    Div a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Mod a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Pow a1 a2 -> Set.union (freeVars a1) (freeVars a2)

instance FreeVariables Assertion where
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
    (Hole _)     -> Set.empty
