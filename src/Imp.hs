module Imp
    ( AbsStmt(..)
    , AExp(..)
    , BExp(..)
    , Prog
    , SFun(..)
    , Stmt
    , Var
    , aexpToZ3
    , assignPost
    , asubst
    , avars
    , bexpToZ3
    , bsubst
    , bvars
    , fsubst
    , prefixAExpVars
    , prefixBExpVars
    , prefixProgVars
    , subAexp
    , subVar
    , svars
    ) where

import qualified Data.Set as Set
import Z3.Monad

type Var = String


----------------------------
-- Arithmetic Expressions --
----------------------------

data AExp
  = ALit Integer
  | AVar Var
  | AAdd AExp AExp
  | ASub AExp AExp
  | AMul AExp AExp
  | ADiv AExp AExp
  | AMod AExp AExp
  deriving (Eq, Ord, Show)

asubst :: AExp -> Var -> AExp -> AExp
asubst aexp var repl =
  case aexp of
    ALit i -> ALit i
    AVar v -> if (v == var) then repl else aexp
    AAdd lhs rhs -> AAdd (asubst lhs var repl) (asubst rhs var repl)
    ASub lhs rhs -> ASub (asubst lhs var repl) (asubst rhs var repl)
    AMul lhs rhs -> AMul (asubst lhs var repl) (asubst rhs var repl)
    ADiv lhs rhs -> ADiv (asubst lhs var repl) (asubst rhs var repl)
    AMod lhs rhs -> AMod (asubst lhs var repl) (asubst rhs var repl)

avars :: AExp -> Set.Set Var
avars aexp =
  case aexp of
    ALit _ -> Set.empty
    AVar v -> Set.singleton v
    AAdd lhs rhs -> Set.union (avars lhs) (avars rhs)
    ASub lhs rhs -> Set.union (avars lhs) (avars rhs)
    AMul lhs rhs -> Set.union (avars lhs) (avars rhs)
    ADiv lhs rhs -> Set.union (avars lhs) (avars rhs)
    AMod lhs rhs -> Set.union (avars lhs) (avars rhs)

aexpToZ3 :: AExp -> Z3 AST
aexpToZ3 aexp =
  case aexp of
    ALit i   -> mkIntNum i
    AVar var -> mkIntVar =<< mkStringSymbol var
    AAdd aexp1 aexp2 -> mkAdd =<< mapM aexpToZ3 [aexp1, aexp2]
    ASub aexp1 aexp2 -> mkSub =<< mapM aexpToZ3 [aexp1, aexp2]
    AMul aexp1 aexp2 -> mkMul =<< mapM aexpToZ3 [aexp1, aexp2]
    ADiv aexp1 aexp2 -> do
      dividend <- aexpToZ3 aexp1
      divisor  <- aexpToZ3 aexp2
      mkMod dividend divisor
    AMod aexp1 aexp2 -> do
      dividend <- aexpToZ3 aexp1
      divisor  <- aexpToZ3 aexp2
      mkMod dividend divisor

subVar :: AST -> Var -> Var -> Z3 AST
subVar ast var repl = subAexp ast (AVar var) (AVar repl)

subAexp :: AST -> AExp -> AExp -> Z3 AST
subAexp ast expr repl = do
  z3Expr <- aexpToZ3 $ expr
  z3Repl <- aexpToZ3 $ repl
  substitute ast [z3Expr] [z3Repl]

assignPost :: Var -> AExp -> AST -> Z3 AST
assignPost var aexp post = do
  z3Var   <- aexpToZ3 $ AVar var
  z3Aexp  <- aexpToZ3 aexp
  eq      <- mkEq z3Var z3Aexp
  mkAnd [eq, post]

prefixAExpVars :: String -> AExp -> AExp
prefixAExpVars pre aexp =
  case aexp of
    ALit i -> ALit i
    AVar v -> AVar $ pre ++ v
    AAdd lhs rhs -> AAdd (prefix lhs) (prefix rhs)
    ASub lhs rhs -> ASub (prefix lhs) (prefix rhs)
    AMul lhs rhs -> AMul (prefix lhs) (prefix rhs)
    ADiv lhs rhs -> ADiv (prefix lhs) (prefix rhs)
    AMod lhs rhs -> AMod (prefix lhs) (prefix rhs)
  where prefix = prefixAExpVars pre


-------------------------
-- Boolean Expressions --
-------------------------

data BExp
  = BTrue
  | BFalse
  | BNot BExp
  | BAnd BExp BExp
  | BOr  BExp BExp
  | BEq  AExp AExp
  | BNe  AExp AExp
  | BLe  AExp AExp
  | BGe  AExp AExp
  | BLt  AExp AExp
  | BGt  AExp AExp
  deriving (Eq, Ord, Show)

bsubst :: BExp -> Var -> AExp -> BExp
bsubst bexp var aexp =
  case bexp of
    BTrue        -> BTrue
    BFalse       -> BFalse
    BNot b       -> BNot (bsubst b var aexp)
    BAnd b1  b2  -> BAnd (bsubst b1 var aexp)  (bsubst b2 var aexp)
    BOr  b1  b2  -> BOr  (bsubst b1 var aexp)  (bsubst b2 var aexp)
    BEq  lhs rhs -> BEq  (asubst lhs var aexp) (asubst rhs var aexp)
    BNe  lhs rhs -> BNe  (asubst lhs var aexp) (asubst rhs var aexp)
    BLe  lhs rhs -> BLe  (asubst lhs var aexp) (asubst rhs var aexp)
    BGe  lhs rhs -> BGe  (asubst lhs var aexp) (asubst rhs var aexp)
    BLt  lhs rhs -> BLt  (asubst lhs var aexp) (asubst rhs var aexp)
    BGt  lhs rhs -> BGt  (asubst lhs var aexp) (asubst rhs var aexp)

bvars :: BExp -> Set.Set Var
bvars bexp =
  case bexp of
    BTrue        -> Set.empty
    BFalse       -> Set.empty
    BNot b       -> bvars b
    BAnd b1  b2  -> Set.union (bvars b1)  (bvars b2)
    BOr  b1  b2  -> Set.union (bvars b1)  (bvars b2)
    BEq  lhs rhs -> Set.union (avars lhs) (avars rhs)
    BNe  lhs rhs -> Set.union (avars lhs) (avars rhs)
    BLe  lhs rhs -> Set.union (avars lhs) (avars rhs)
    BGe  lhs rhs -> Set.union (avars lhs) (avars rhs)
    BLt  lhs rhs -> Set.union (avars lhs) (avars rhs)
    BGt  lhs rhs -> Set.union (avars lhs) (avars rhs)

bexpToZ3 :: BExp -> Z3 AST
bexpToZ3 bexp =
  case bexp of
    BTrue        -> mkTrue
    BFalse       -> mkFalse
    BNot b       -> mkNot =<< bexpToZ3 b
    BAnd b1  b2  -> mkAnd =<< mapM bexpToZ3 [b1, b2]
    BOr  b1  b2  -> mkOr  =<< mapM bexpToZ3 [b1, b2]
    BEq  lhs rhs -> do
      lhsAST <- aexpToZ3 lhs
      rhsAST <- aexpToZ3 rhs
      mkEq lhsAST rhsAST
    BNe  lhs rhs -> do
      lhsAST <- aexpToZ3 lhs
      rhsAST <- aexpToZ3 rhs
      mkNot =<< mkEq lhsAST rhsAST
    BLe  lhs rhs -> do
      lhsAST <- aexpToZ3 lhs
      rhsAST <- aexpToZ3 rhs
      mkLe lhsAST rhsAST
    BGe  lhs rhs -> do
      lhsAST <- aexpToZ3 lhs
      rhsAST <- aexpToZ3 rhs
      mkGe lhsAST rhsAST
    BGt  lhs rhs -> do
      lhsAST <- aexpToZ3 lhs
      rhsAST <- aexpToZ3 rhs
      mkGt lhsAST rhsAST
    BLt  lhs rhs -> do
      lhsAST <- aexpToZ3 lhs
      rhsAST <- aexpToZ3 rhs
      mkLt lhsAST rhsAST

prefixBExpVars :: String -> BExp -> BExp
prefixBExpVars pre bexp =
  case bexp of
    BTrue        -> BTrue
    BFalse       -> BFalse
    BNot b       -> BNot $ prefixB b
    BAnd b1  b2  -> BAnd (prefixB b1)  (prefixB b2)
    BOr  b1  b2  -> BOr  (prefixB b1)  (prefixB b2)
    BEq  lhs rhs -> BEq  (prefixA lhs) (prefixA rhs)
    BNe  lhs rhs -> BNe  (prefixA lhs) (prefixA rhs)
    BLe  lhs rhs -> BLe  (prefixA lhs) (prefixA rhs)
    BGe  lhs rhs -> BGe  (prefixA lhs) (prefixA rhs)
    BLt  lhs rhs -> BLt  (prefixA lhs) (prefixA rhs)
    BGt  lhs rhs -> BGt  (prefixA lhs) (prefixA rhs)
  where
    prefixA = prefixAExpVars pre
    prefixB = prefixBExpVars pre


---------------
-- Functions --
---------------

data SFun = SFun
  { fName     :: String
  , fParams   :: [Var]
  } deriving (Eq, Ord, Show)

fsubst :: SFun -> Var -> Var -> Z3 SFun
fsubst (SFun name params) var repl = do
  let params' = map (\p -> if p == var then repl else p) params
  return $ SFun name params'


---------------------------
-- Statements / Programs --
---------------------------

-- Parameterized over the type of loop specs.
-- This allows the parser to return SMT strings
-- instead of conflating Z3 interaction with
-- parsing to construct Z3 ASTs at parse time.

data AbsStmt a
  = SSkip
  | SAsgn  Var AExp
  | SSeq   [AbsStmt a]
  | SIf    BExp (AbsStmt a) (AbsStmt a)
  | SWhile BExp (AbsStmt a) (a, a)
  | SCall  Var  SFun
  deriving (Eq, Ord, Show)

type Stmt       = AbsStmt AST
type Prog       = Stmt

svars :: AbsStmt a -> Set.Set Var
svars stmt = case stmt of
  SSkip                   -> Set.empty
  SAsgn  var aexp         -> Set.insert var $ avars aexp
  SSeq   []               -> svars SSkip
  SSeq   (s:ss)           -> Set.union (svars s) (svars $ SSeq ss)
  SIf    cond bThen bElse -> Set.unions
                               [(bvars cond), (svars bThen), (svars bElse)]
  SWhile cond body _      -> Set.union (bvars cond) (svars body)
  SCall  var  fun         -> Set.singleton var

prefixProgVars :: String -> AbsStmt a -> AbsStmt a
prefixProgVars pre prog =
  case prog of
    SSkip                 -> SSkip
    SAsgn  var aexp       -> SAsgn  (pre ++ var) (prefixA aexp)
    SSeq   stmts          -> SSeq $ map prefixP stmts
    SIf    cond s1 s2     -> SIf    (prefixB cond) (prefixP s1) (prefixP s2)
    SWhile cond body spec -> SWhile (prefixB cond) (prefixP body) spec
    SCall  var  (SFun fname fparams) -> SCall (prefix var) $
      SFun (prefix fname) (map prefix fparams)
  where
    prefix s = pre ++ s
    prefixA = prefixAExpVars pre
    prefixB = prefixBExpVars pre
    prefixP = prefixProgVars pre
