module Assertion
  ( Arith(..)
  , Assertion(..)
  , Ident(..)
  , Name
  , Sort(..)
  , subArith
  , toSMT
  ) where

import           Data.List ( intercalate )
import           MapNames
import           SMTMonad  ( SMT )
import qualified SMTMonad as SMT


-----------------
-- Identifiers --
-----------------

type Name = String

data Sort = Int
          -- Add support for other sorts as needed.
          deriving (Eq, Ord)

data Ident = Ident { identName :: Name
                   , identSort :: Sort
                   }
           deriving (Eq, Ord)

instance Show Sort where
  show Int  = "int"

instance Show Ident where
  show (Ident name sort) = "(" ++ name ++ " " ++ (show sort) ++ ")"

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
           | Pow Arith Arith
           | Mod Arith Arith
           deriving (Eq, Ord)

showSexp :: Show a => String -> [a] -> String
showSexp name as = "(" ++ name ++ " " ++ (intercalate " " $ map show as) ++ ")"

instance Show Arith where
  show (Num n)     = show n
  show (Var ident) = identName ident
  show (Add as)    = showSexp "+"  as
  show (Sub as)    = showSexp "-"  as
  show (Mul as)    = showSexp "*"  as
  show (Div a1 a2) = showSexp "/"  [a1, a2]
  show (Pow a1 a2) = showSexp "^"  [a1, a2]
  show (Mod a1 a2) = showSexp "%"  [a1, a2]

instance MappableNames Arith where
  mapNames _ (Num x)     = Num x
  mapNames f (Var ident) = Var (mapNames f ident)
  mapNames f (Add as)    = Add $ map (mapNames f) as
  mapNames f (Sub as)    = Sub $ map (mapNames f) as
  mapNames f (Mul as)    = Mul $ map (mapNames f) as
  mapNames f (Div a1 a2) = Div (mapNames f a1) (mapNames f a2)
  mapNames f (Pow a1 a2) = Pow (mapNames f a1) (mapNames f a2)
  mapNames f (Mod a1 a2) = Mod (mapNames f a1) (mapNames f a2)


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
               deriving (Eq, Ord)

showQuant :: Show a => String -> [Ident] -> a -> String
showQuant name qvars body = "(" ++ name ++ " "
                                ++ (intercalate " " $ map show qvars)
                                ++ (show body) ++ ")"

instance Show Assertion where
  show ATrue           = "true"
  show AFalse          = "false"
  show (Atom ident)    = identName ident
  show (Not a)         = showSexp "!" [a]
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
      Pow a1 a2 -> Pow (sub a1) (sub a2)
      Mod a1 a2 -> Mod (sub a1) (sub a2)

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


-------------------
-- SMT Embedding --
-------------------

class SMTEmbeddable a where
  toSMT :: a -> SMT SMT.Expr

instance SMTEmbeddable Ident where
  toSMT (Ident name sort) = do
    nameSymb <- SMT.mkStringSymbol name
    case sort of
      Int  -> SMT.mkIntVar nameSymb

instance SMTEmbeddable Arith where
  toSMT (Num n)     = SMT.mkIntNum n
  toSMT (Var ident) = toSMT ident
  toSMT (Add as)    = SMT.mkAdd =<< mapM toSMT as
  toSMT (Sub as)    = SMT.mkSub =<< mapM toSMT as
  toSMT (Mul as)    = SMT.mkMul =<< mapM toSMT as
  toSMT (Div a1 a2) = bind2 SMT.mkDiv   (toSMT a1) (toSMT a2)
  toSMT (Pow a1 a2) = bind2 SMT.mkPower (toSMT a1) (toSMT a2)
  toSMT (Mod a1 a2) = bind2 SMT.mkMod   (toSMT a1) (toSMT a2)

instance SMTEmbeddable Assertion where
  toSMT ATrue         = SMT.mkTrue
  toSMT AFalse        = SMT.mkFalse
  toSMT (Atom ident)  = toSMT ident
  toSMT (Not a)       = SMT.mkNot =<< toSMT a
  toSMT (And as)      = SMT.mkAnd =<< mapM toSMT as
  toSMT (Or as)       = SMT.mkOr  =<< mapM toSMT as
  toSMT (Imp a1 a2)   = bind2 SMT.mkImplies (toSMT a1) (toSMT a2)
  toSMT (Eq a1 a2)    = bind2 SMT.mkEq (toSMT a1) (toSMT a2)
  toSMT (Lt a1 a2)    = bind2 SMT.mkLt (toSMT a1) (toSMT a2)
  toSMT (Gt a1 a2)    = bind2 SMT.mkGt (toSMT a1) (toSMT a2)
  toSMT (Lte a1 a2)   = bind2 SMT.mkLe (toSMT a1) (toSMT a2)
  toSMT (Gte a1 a2)   = bind2 SMT.mkGe (toSMT a1) (toSMT a2)
  toSMT (Forall vs a) = bind2 SMT.mkForallConst
                          (SMT.stringsToApps $ map identName vs)
                          (toSMT a)
  toSMT (Exists vs a) = bind2 SMT.mkExistsConst
                          (SMT.stringsToApps $ map identName vs)
                          (toSMT a)

bind2 :: Monad m => (a -> b -> m c) -> m a -> m b -> m c
bind2 f ma mb = do
  a <- ma
  b <- mb
  f a b
