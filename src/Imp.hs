module Imp
    ( AExp(..)
    , aexpToZ3
    , asubst
    , avars
    , BExp(..)
    , bsubst
    , bvars
    , fsubst
    , Prog
    , Stmt(..)
    , UFunc(..)
    , Var
    ) where

import Z3.Monad

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
    I i -> []
    V v -> [v]
    lhs :+: rhs -> (avars lhs) ++ (avars rhs)
    lhs :-: rhs -> (avars lhs) ++ (avars rhs)
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
      divisor <- aexpToZ3 aexp2
      mkMod dividend divisor


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

impl :: BExp -> BExp -> BExp
impl bexp1 bexp2 = bsimpl $ BOr (BNot bexp1) bexp2

bsimpl :: BExp -> BExp
bsimpl (BNot (BNot bexp)) = bexp
bsimpl (BNot bexp) = BNot (bsimpl bexp)
bsimpl (BAnd bexp1 bexp2) = BAnd (bsimpl bexp1) (bsimpl bexp2)
bsimpl bexp = bexp

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


-----------------------------
-- Uninterpreted Functions --
-----------------------------

data UFunc = UFunc
  { fName     :: String
  , fParams   :: [Var]
  , fPreBexp  :: BExp
  , fPostBexp :: BExp
  } deriving (Eq, Ord, Show)

fsubst :: UFunc -> Var -> Var -> UFunc
fsubst (UFunc name params pre post) var repl =
  UFunc name params' pre post
  where
    params' = map (\p -> if p == var then repl else p) params


---------------------------
-- Statements / Programs --
---------------------------

data Stmt
  = Skip
  | Var := AExp
  | Seq [Stmt]
  | If BExp Stmt Stmt
  | Call Var UFunc
  deriving (Eq, Ord, Show)

type Prog = Stmt
