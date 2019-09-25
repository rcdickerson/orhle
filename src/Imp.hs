module Imp
    ( AExp(..)
    , BExp(..)
    , Prog
    , Stmt(..)
    , Func(..)
    , Var
    , aexpToZ3
    , assignPost
    , asubst
    , avars
    , bexpToZ3
    , bsubst
    , bvars
    , fsubst
    , subAexp
    , subVar
    ) where

import Z3.Monad
import Z3Util

infix 1 :=
infix 2 :=:
infixl 6 :+:, :-:
infixl 7 :*:

type Var = String

----------------------------
-- Arithmetic Expressions --
----------------------------

data AExp
  = I Integer
  | V Var
  | AExp :+: AExp
  | AExp :-: AExp
  | AExp :*: AExp
  | AMod AExp AExp
  deriving (Eq, Ord, Show)

asubst :: AExp -> Var -> AExp -> AExp
asubst aexp var repl =
  case aexp of
    I i -> I i
    V v -> if (v == var) then repl else aexp
    lhs :+: rhs -> (asubst lhs var repl) :+: (asubst rhs var repl)
    lhs :-: rhs -> (asubst lhs var repl) :-: (asubst rhs var repl)
    lhs :*: rhs -> (asubst lhs var repl) :*: (asubst rhs var repl)
    AMod lhs rhs -> AMod (asubst lhs var repl) (asubst rhs var repl)

avars :: AExp -> [Var]
avars aexp =
  case aexp of
    I _          -> []
    V v          -> [v]
    lhs :+: rhs  -> (avars lhs) ++ (avars rhs)
    lhs :-: rhs  -> (avars lhs) ++ (avars rhs)
    lhs :*: rhs  -> (avars lhs) ++ (avars rhs)
    AMod lhs rhs -> (avars lhs) ++ (avars rhs)

aexpToZ3 :: AExp -> Z3 AST
aexpToZ3 aexp =
  case aexp of
    I i -> mkIntNum i
    V var -> mkIntVar =<< mkStringSymbol var
    aexp1 :+: aexp2 -> mkAdd =<< mapM aexpToZ3 [aexp1, aexp2]
    aexp1 :-: aexp2 -> mkSub =<< mapM aexpToZ3 [aexp1, aexp2]
    aexp1 :*: aexp2 -> mkMul =<< mapM aexpToZ3 [aexp1, aexp2]
    AMod aexp1 aexp2 -> do
      dividend <- aexpToZ3 aexp1
      divisor  <- aexpToZ3 aexp2
      mkMod dividend divisor

subVar :: AST -> Var -> Var -> Z3 AST
subVar ast var repl = subAexp ast (V var) (V repl)

subAexp :: AST -> AExp -> AExp -> Z3 AST
subAexp ast expr repl = do
  z3Expr <- aexpToZ3 $ expr
  z3Repl <- aexpToZ3 $ repl
  substitute ast [z3Expr] [z3Repl]

assignPost :: Var -> AExp -> AST -> Z3 AST
assignPost var aexp post = do
  z3Var   <- aexpToZ3 $ V var
  z3Aexp  <- aexpToZ3 aexp
  eq      <- mkEq z3Var z3Aexp
  mkAnd [eq, post]


-------------------------
-- Boolean Expressions --
-------------------------

data BExp
  = BTrue
  | BFalse
  | AExp :=: AExp
  | BNot BExp
  | BAnd BExp BExp
  | BOr BExp BExp
  deriving (Eq, Ord, Show)

bsubst :: BExp -> Var -> AExp -> BExp
bsubst bexp var aexp =
  case bexp of
    BTrue -> BTrue
    BFalse -> BFalse
    lhs :=: rhs -> (asubst lhs var aexp) :=: (asubst rhs var aexp)
    BNot b -> BNot (bsubst b var aexp)
    BAnd b1 b2 -> BAnd (bsubst b1 var aexp) (bsubst b2 var aexp)
    BOr b1 b2 -> BOr (bsubst b1 var aexp) (bsubst b2 var aexp)

bvars :: BExp -> [Var]
bvars bexp =
  case bexp of
    BTrue -> []
    BFalse -> []
    lhs :=: rhs -> (avars lhs) ++ (avars rhs)
    BNot b -> bvars b
    BAnd b1 b2 -> (bvars b1) ++ (bvars b2)
    BOr b1 b2 -> (bvars b1) ++ (bvars b2)

bexpToZ3 :: BExp -> Z3 AST
bexpToZ3 bexp =
  case bexp of
    BTrue -> mkTrue
    BFalse -> mkFalse
    lhs :=: rhs -> do
      lhsAST <- aexpToZ3 lhs
      rhsAST <- aexpToZ3 rhs
      mkEq lhsAST rhsAST
    BNot b -> mkNot =<< bexpToZ3 b
    BAnd b1 b2 -> mkAnd =<< mapM bexpToZ3 [b1, b2]
    BOr  b1 b2 -> mkOr  =<< mapM bexpToZ3 [b1, b2]


---------------
-- Functions --
---------------

data Func = Func
  { fName     :: String
  , fParams   :: [Var]
  } deriving (Eq, Ord, Show)

fsubst :: Func -> Var -> Var -> Z3 Func
fsubst f@(Func name params) var repl = do
  let params' = map (\p -> if p == var then repl else p) params
  return $ Func name params'


---------------------------
-- Statements / Programs --
---------------------------

data Stmt
  = Skip
  | Var := AExp
  | Seq [Stmt]
  | If BExp Stmt Stmt
  | Call Var Func
  deriving (Eq, Ord, Show)

type Prog = Stmt
