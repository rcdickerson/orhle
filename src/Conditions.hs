module Conditions where

import Imp
import Z3.Monad

data Cond
  = CTrue
  | CFalse
  | CEq AExp AExp
  | CNot Cond
  | CAnd Cond Cond
  | COr Cond Cond
  | CImp Cond Cond
  | CAssignPost Var AExp Cond
  | CAbducible String [Var]
  deriving (Show)

condToZ3 :: Cond -> Z3 AST
condToZ3 cond =
  case cond of
    CTrue -> mkTrue
    CFalse -> mkFalse
    CEq aexp1 aexp2 -> do
      z3Exp1 <- aexpToZ3 aexp1
      z3Exp2 <- aexpToZ3 aexp2
      mkEq z3Exp1 z3Exp2
    CNot cexp -> mkNot =<< condToZ3 cexp
    CAnd cexp1 cexp2 -> mkAnd =<< mapM condToZ3 [cexp1, cexp2]
    COr  cexp1 cexp2 -> mkOr  =<< mapM condToZ3 [cexp1, cexp2]
    CImp cexp1 cexp2 -> do
      p <- condToZ3 cexp1
      q <- condToZ3 cexp2
      mkImplies p q
    CAssignPost var aexp cond -> do
      freshVar <- mkFreshIntVar var
      freshVarStr <- astToString freshVar
      body <- condToZ3 $ CAnd (CEq (V freshVarStr) (aexp))
                              (csubst cond var (V freshVarStr))
      const <- toApp freshVar
      mkExistsConst [] [const] body
    CAbducible fName args -> do
      argSorts <- mapM (\x -> mkIntSort) args
      args <- mapM (aexpToZ3.V) args
      retSort <- mkBoolSort
      abdName <- mkStringSymbol fName
      abducible <- mkFuncDecl abdName argSorts retSort
      mkApp abducible args

csubst :: Cond -> Var -> AExp -> Cond
csubst cond var repl =
  case cond of
    CTrue -> CTrue
    CFalse -> CFalse
    CEq lhs rhs -> CEq (asubst lhs var repl) (asubst rhs var repl)
    CNot c -> CNot (csubst c var repl)
    CAnd c1 c2 -> CAnd (csubst c1 var repl) (csubst c2 var repl)
    COr c1 c2 -> COr (csubst c1 var repl) (csubst c2 var repl)
    CImp c1 c2 -> CImp (csubst c1 var repl) (csubst c2 var repl)
    CAssignPost v a c -> CAssignPost
        v -- TODO: replace here?
        (asubst a var repl)
        (csubst c var repl)
    -- TODO: replace over args?
    CAbducible fName args -> CAbducible fName args

bexpToCond :: BExp -> Cond
bexpToCond bexp =
  case bexp of
    BTrue -> CTrue
    BFalse -> CFalse
    (:=:) lhs rhs -> CEq lhs rhs
    BNot b -> CNot $ bexpToCond b
    BAnd b1 b2 -> CAnd (bexpToCond b1) (bexpToCond b2)
