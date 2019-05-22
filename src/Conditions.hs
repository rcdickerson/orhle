module Conditions
    ( bexpToCond
    , Cond(..)
    , condToZ3
    , csubst
    ) where

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
  | CAbducible Cond UFunc
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
      condToZ3 $ CAnd (CEq (V var) (asubst aexp var (V freshVarStr)))
                      (csubst cond var (V freshVarStr))
    CAbducible pre (UFunc fName fParams fPre fPost) -> do
      argSorts <- mapM (\_ -> mkIntSort) fParams
      args <- mapM (aexpToZ3.V) fParams
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
    asgn@(CAssignPost v a c) ->
      case repl of
        V replVar -> CAssignPost
            (if v == var then replVar else v)
            (asubst a var repl)
            (csubst c var repl)
        _ -> asgn
    abd@(CAbducible pre (UFunc name params fPre fPost)) ->
      case repl of
        V replVar -> CAbducible (csubst pre var repl)
          (UFunc name subParams fPre fPost)
          where subParams = map (\x -> (if x == var then replVar else x)) params
        _ -> abd

bexpToCond :: BExp -> Cond
bexpToCond bexp =
  case bexp of
    BTrue -> CTrue
    BFalse -> CFalse
    (:=:) lhs rhs -> CEq lhs rhs
    BNot b -> CNot $ bexpToCond b
    BAnd b1 b2 -> CAnd (bexpToCond b1) (bexpToCond b2)
    BOr b1 b2 -> COr (bexpToCond b1) (bexpToCond b2)
