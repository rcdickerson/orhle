module Imp
    ( AExp(..)
    , aexpToZ3
    , assignPost
    , asubst
    , avars
    , BExp(..)
    , bexpToZ3
    , bsubst
    , bvars
    , fPostCondAST
    , fPreCondAST
    , fsubst
    , funSP
    , subAexp
    , subVar
    , Prog
    , Stmt(..)
    , UFunc(..)
    , Var
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

subVar :: SMTString -> Var -> Var -> Z3 SMTString
subVar smt var repl = do
  ast    <- parseSMT smt
  z3Var  <- aexpToZ3 $ V var
  z3Repl <- aexpToZ3 $ V repl
  smtString =<< substituteVars ast [z3Var, z3Repl]

subAexp :: SMTString -> AExp -> AExp -> Z3 SMTString
subAexp smt lhs rhs = do
  ast   <- parseSMT smt
  z3Lhs <- aexpToZ3 $ lhs
  z3Rhs <- aexpToZ3 $ rhs
  smtString =<< substituteVars ast [z3Lhs, z3Rhs]

assignPost :: Var -> AExp -> SMTString -> Z3 SMTString
assignPost var aexp post = do
  z3Var   <- aexpToZ3 $ V var
  z3Aexp  <- aexpToZ3 aexp
  eq      <- mkEq z3Var z3Aexp
  postAST <- parseSMT post
  smtString =<< mkAnd [eq, postAST]


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


-----------------------------
-- Uninterpreted Functions --
-----------------------------

data UFunc = UFunc
  { fName     :: String
  , fParams   :: [Var]
  , fPreCond  :: String
  , fPostCond :: String
  } deriving (Eq, Ord, Show)

fsubst :: UFunc -> Var -> Var -> Z3 UFunc
fsubst f@(UFunc name params _ _) var repl = do
  pre'  <- subAST $ fPreCond  f
  post' <- subAST $ fPostCond f
  let params' = map (\p -> if p == var then repl else p) params
  return $ UFunc name params' pre' post'
  where
    subAST ast = subVar ast var repl

fPreCondAST :: UFunc -> Z3 AST
fPreCondAST = parseSMT.fPreCond

fPostCondAST :: UFunc -> Z3 AST
fPostCondAST = parseSMT.fPostCond

funSP :: UFunc -> SMTString -> Z3 SMTString
funSP f pre = do
  preAST  <- parseSMT pre
  postAST <- fPostCondAST f
  smtString =<< mkAnd [preAST, postAST]


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
