module Orhle.Imp.ImpLanguage
    ( AExp(..)
    , BExp(..)
    , SFun(..)
    , Stmt(..)
    , Var
    , aexpToArith
    , avars
    , bexpToAssertion
    , bvars
    , svars
    ) where

import qualified Data.Set  as Set
import           Orhle.Assertion.AssertionLanguage  ( Assertion)
import qualified Orhle.Assertion.AssertionLanguage as A
import           Orhle.MapNames


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
  | APow AExp AExp
  deriving (Eq, Ord, Show)

instance MappableNames AExp where
  mapNames _ (ALit i)       = ALit i
  mapNames f (AVar v)       = AVar (f v)
  mapNames f (AAdd lhs rhs) = AAdd (mapNames f lhs) (mapNames f rhs)
  mapNames f (ASub lhs rhs) = ASub (mapNames f lhs) (mapNames f rhs)
  mapNames f (AMul lhs rhs) = AMul (mapNames f lhs) (mapNames f rhs)
  mapNames f (ADiv lhs rhs) = ADiv (mapNames f lhs) (mapNames f rhs)
  mapNames f (AMod lhs rhs) = AMod (mapNames f lhs) (mapNames f rhs)
  mapNames f (APow lhs rhs) = APow (mapNames f lhs) (mapNames f rhs)

avars :: AExp -> Set.Set Var
avars aexp = case aexp of
  ALit _ -> Set.empty
  AVar v -> Set.singleton v
  AAdd lhs rhs -> Set.union (avars lhs) (avars rhs)
  ASub lhs rhs -> Set.union (avars lhs) (avars rhs)
  AMul lhs rhs -> Set.union (avars lhs) (avars rhs)
  ADiv lhs rhs -> Set.union (avars lhs) (avars rhs)
  AMod lhs rhs -> Set.union (avars lhs) (avars rhs)
  APow lhs rhs -> Set.union (avars lhs) (avars rhs)

aexpToArith :: AExp -> A.Arith
aexpToArith aexp = case aexp of
  ALit i           -> A.Num i
  AVar var         -> A.Var (A.Ident var A.Int)
  AAdd aexp1 aexp2 -> A.Add [aexpToArith aexp1, aexpToArith aexp2]
  ASub aexp1 aexp2 -> A.Sub [aexpToArith aexp1, aexpToArith aexp2]
  AMul aexp1 aexp2 -> A.Mul [aexpToArith aexp1, aexpToArith aexp2]
  ADiv aexp1 aexp2 -> let
    dividend = aexpToArith aexp1
    divisor  = aexpToArith aexp2
    in A.Div dividend divisor
  AMod aexp1 aexp2 -> let
    dividend = aexpToArith aexp1
    divisor  = aexpToArith aexp2
    in A.Mod dividend divisor
  APow aexp1 aexp2 -> let
    base  = aexpToArith aexp1
    power = aexpToArith aexp2
    in A.Pow base power


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

instance MappableNames BExp where
  mapNames _ BTrue        = BTrue
  mapNames _ BFalse       = BFalse
  mapNames f (BNot b)     = BNot $ mapNames f b
  mapNames f (BAnd b1 b2) = BAnd (mapNames f b1) (mapNames f b2)
  mapNames f (BOr b1 b2)  = BOr (mapNames f b1) (mapNames f b2)
  mapNames f (BEq a1 a2)  = BEq (mapNames f a1) (mapNames f a2)
  mapNames f (BNe a1 a2)  = BNe (mapNames f a1) (mapNames f a2)
  mapNames f (BLe a1 a2)  = BLe (mapNames f a1) (mapNames f a2)
  mapNames f (BGe a1 a2)  = BGe (mapNames f a1) (mapNames f a2)
  mapNames f (BLt a1 a2)  = BLt (mapNames f a1) (mapNames f a2)
  mapNames f (BGt a1 a2)  = BGt (mapNames f a1) (mapNames f a2)

bvars :: BExp -> Set.Set Var
bvars bexp = case bexp of
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

bexpToAssertion :: BExp -> Assertion
bexpToAssertion bexp = case bexp of
  BTrue      -> A.ATrue
  BFalse     -> A.AFalse
  BNot b     -> A.Not $ bexpToAssertion b
  BAnd b1 b2 -> A.And [bexpToAssertion b1, bexpToAssertion b2]
  BOr  b1 b2 -> A.Or  [bexpToAssertion b1, bexpToAssertion b2]
  BEq  a1 a2 -> A.Eq  (aexpToArith a1) (aexpToArith a2)
  BNe  a1 a2 -> A.Not $ A.Eq (aexpToArith a1) (aexpToArith a2)
  BLe  a1 a2 -> A.Lte (aexpToArith a1) (aexpToArith a2)
  BGe  a1 a2 -> A.Gte (aexpToArith a1) (aexpToArith a2)
  BGt  a1 a2 -> A.Gt  (aexpToArith a1) (aexpToArith a2)
  BLt  a1 a2 -> A.Lt  (aexpToArith a1) (aexpToArith a2)


---------------
-- Functions --
---------------

data SFun = SFun
  { fName     :: String
  , fParams   :: [Var]
  } deriving (Eq, Ord, Show)

instance MappableNames SFun where
  mapNames f (SFun name params) = SFun (f name) (map f params)


----------------
-- Statements --
----------------
data Stmt
  = SSkip
  | SAsgn  Var AExp
  | SSeq   [Stmt]
  | SIf    BExp Stmt Stmt
  | SWhile BExp Stmt (Assertion, A.Arith, Bool)
  | SCall  [Var] [Var] String
  deriving (Eq, Ord, Show)

instance MappableNames Stmt where
  mapNames _ SSkip          = SSkip
  mapNames f (SAsgn v aexp) = SAsgn (f v) (mapNames f aexp)
  mapNames f (SSeq stmts)   = SSeq $ map (mapNames f) stmts
  mapNames f (SIf b t e)    = SIf (mapNames f b) (mapNames f t) (mapNames f e)
  mapNames f (SWhile cond body (inv, var, local)) =
    SWhile (mapNames f cond) (mapNames f body) (inv, var, local)
  mapNames f (SCall as ps name) =
    SCall (map f as) (map f ps) (f name)

svars :: Stmt -> Set.Set Var
svars stmt = case stmt of
  SSkip                      -> Set.empty
  SAsgn  var aexp            -> Set.insert var $ avars aexp
  SSeq   []                  -> svars SSkip
  SSeq   (s:ss)              -> Set.union (svars s) (svars $ SSeq ss)
  SIf    cond bThen bElse    -> Set.unions
                                  [(bvars cond), (svars bThen), (svars bElse)]
  SWhile cond body _         -> Set.union (bvars cond) (svars body)
  SCall  assignees params  _ -> Set.fromList $ assignees ++ params
