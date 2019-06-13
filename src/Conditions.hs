module Conditions
    ( bexpToCond
    , Cond(..)
    , condToZ3
    , condZ3String
    , conjoin
    , csubst
    , cvars
    , fPreCond
    , fPostCond
    ) where

import Data.Set (Set, empty, toList, fromList, union)
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
  | CFuncPost Var UFunc Cond
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
    CAssignPost var aexp p -> do
      --freshVar <- mkFreshIntVar var
      --freshVarStr <- astToString freshVar
      --condToZ3 $ CAnd (CEq (V var) (asubst aexp var (V freshVarStr)))
      --                (csubst p var (V freshVarStr))
      condToZ3 $ CAnd (CEq (V var) aexp) p
    CFuncPost var f pre -> do
      --freshVar    <- mkFreshIntVar var
      --freshVarStr <- astToString freshVar
      --let fPreSubst  = csubst (fPreCond f)  var (V freshVarStr)
      --let fPostSubst = csubst (fPostCond f) var (V freshVarStr)
      --let preSubst   = csubst pre           var (V freshVarStr)
      --condToZ3 $ CAnd (CAnd fPreSubst fPostSubst) preSubst
      condToZ3 $ CAnd pre (fPostCond f)

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
    fpost@(CFuncPost v f pre) ->
      case repl of
        V replVar -> CFuncPost
            (if v == var then replVar else v)
            (fsubst f v replVar)
            (csubst pre var repl)
        _ -> fpost

bexpToCond :: BExp -> Cond
bexpToCond bexp =
  case bexp of
    BTrue -> CTrue
    BFalse -> CFalse
    (:=:) lhs rhs -> CEq lhs rhs
    BNot b -> CNot $ bexpToCond b
    BAnd b1 b2 -> CAnd (bexpToCond b1) (bexpToCond b2)
    BOr b1 b2 -> COr (bexpToCond b1) (bexpToCond b2)

fPreCond :: UFunc -> Cond
fPreCond = bexpToCond . fPreBexp

fPostCond :: UFunc -> Cond
fPostCond = bexpToCond . fPostBexp

conjoin :: [Cond] -> Cond
conjoin []     = CTrue
conjoin (c:[]) = c
conjoin (c:cs) = CAnd c (conjoin cs)

cvars :: Cond -> [Var]
cvars = toList.cvars'

cvars' :: Cond -> Set Var
cvars' cond =
  case cond of
    CTrue -> empty
    CFalse -> empty
    CEq lhs rhs -> fromList $ (avars lhs) ++ (avars rhs)
    CNot c -> cvars' c
    CAnd c1 c2 -> (cvars' c1) `union` (cvars' c2)
    COr c1 c2 -> (cvars' c1) `union` (cvars' c2)
    CImp c1 c2 -> fromList $ (cvars c1) ++ (cvars c2)
    CAssignPost v a c -> fromList $ v : (avars a) ++ (cvars c)
    CFuncPost v f pre -> fromList $ v : (cvars pre) ++ (fParams f)

condZ3String :: Cond -> Z3 String
condZ3String cond = astToString =<< simplify =<< condToZ3 cond
