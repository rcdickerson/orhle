module Orhle.Imp.ImpLanguage
    ( AExp(..)
    , BExp(..)
    , Program(..)
    , SFun(..)
    , Var
    , aexpToArith
    , avars
    , bexpToAssertion
    , bvars
    , fillInvHole
    , invHoleIds
    , plits
    , pvars
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

alits :: AExp -> Set.Set Integer
alits aexp = case aexp of
  ALit i -> Set.singleton i
  AVar v -> Set.empty
  AAdd lhs rhs -> Set.union (alits lhs) (alits rhs)
  ASub lhs rhs -> Set.union (alits lhs) (alits rhs)
  AMul lhs rhs -> Set.union (alits lhs) (alits rhs)
  ADiv lhs rhs -> Set.union (alits lhs) (alits rhs)
  AMod lhs rhs -> Set.union (alits lhs) (alits rhs)
  APow lhs rhs -> Set.union (alits lhs) (alits rhs)

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

blits :: BExp -> Set.Set Integer
blits bexp = case bexp of
  BTrue        -> Set.empty
  BFalse       -> Set.empty
  BNot b       -> blits b
  BAnd b1  b2  -> Set.union (blits b1)  (blits b2)
  BOr  b1  b2  -> Set.union (blits b1)  (blits b2)
  BEq  lhs rhs -> Set.union (alits lhs) (alits rhs)
  BNe  lhs rhs -> Set.union (alits lhs) (alits rhs)
  BLe  lhs rhs -> Set.union (alits lhs) (alits rhs)
  BGe  lhs rhs -> Set.union (alits lhs) (alits rhs)
  BLt  lhs rhs -> Set.union (alits lhs) (alits rhs)
  BGt  lhs rhs -> Set.union (alits lhs) (alits rhs)

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
-- Programs --
----------------
data Program
  = SSkip
  | SAsgn  Var AExp
  | SSeq   [Program]
  | SIf    BExp Program Program
  | SWhile BExp Program (Assertion, A.Arith)
  | SCall  [Var] [Var] String
  deriving (Eq, Ord, Show)

instance MappableNames Program where
  mapNames _ SSkip          = SSkip
  mapNames f (SAsgn v aexp) = SAsgn (f v) (mapNames f aexp)
  mapNames f (SSeq stmts)   = SSeq $ map (mapNames f) stmts
  mapNames f (SIf b t e)    = SIf (mapNames f b) (mapNames f t) (mapNames f e)
  mapNames f (SWhile cond body (inv, var)) =
    SWhile (mapNames f cond) (mapNames f body) (inv, var)
  mapNames f (SCall as ps name) =
    SCall (map f as) (map f ps) (f name)

pvars :: Program -> Set.Set Var
pvars prog = case prog of
  SSkip                      -> Set.empty
  SAsgn  var aexp            -> Set.insert var $ avars aexp
  SSeq   []                  -> Set.empty
  SSeq   (s:ss)              -> Set.union (pvars s) (pvars $ SSeq ss)
  SIf    cond bThen bElse    -> Set.unions
                                  [(bvars cond), (pvars bThen), (pvars bElse)]
  SWhile cond body _         -> Set.union (bvars cond) (pvars body)
  SCall  assignees params  _ -> Set.fromList $ assignees ++ params

plits :: Program -> Set.Set Integer
plits prog = case prog of
  SSkip                   -> Set.empty
  SAsgn  var aexp         -> alits aexp
  SSeq   []               -> Set.empty
  SSeq   (s:ss)           -> Set.union (plits s) (plits $ SSeq ss)
  SIf    cond bThen bElse -> Set.unions
                               [(blits cond), (plits bThen), (plits bElse)]
  SWhile cond body _      -> Set.union (blits cond) (plits body)
  SCall  _ _ _            -> Set.empty


invHoleIds :: Program -> Set.Set Int
invHoleIds prog = case prog of
  SSkip       -> Set.empty
  SAsgn _ _   -> Set.empty
  SSeq ps     -> Set.unions $ map invHoleIds ps
  SIf _ p1 p2 -> Set.union (invHoleIds p1) (invHoleIds p2)
  SCall _ _ _ -> Set.empty
  SWhile _ body (inv, _) -> Set.union (invHoleIds body) $
    case inv of
      A.Hole hid -> Set.singleton hid
      _          -> Set.empty

fillInvHole :: Program -> Int -> Assertion -> Program
fillInvHole prog holeId fill = let
  fillRec p = fillInvHole p holeId fill
  in case prog of
    SSkip            -> SSkip
    SAsgn v a        -> SAsgn v a
    SSeq ps          -> SSeq $ map fillRec ps
    SIf c p1 p2      -> SIf c (fillRec p1) (fillRec p2)
    SCall as ps name -> SCall as ps name
    SWhile c body (inv, var) ->
      let inv' = case inv of
            A.Hole hid -> if hid == holeId then fill else inv
            _          -> inv
      in SWhile c (fillRec body) (inv', var)
