module Verifier where

import Imp
import Z3.Monad

type Cond = BExp

data HTrip = HTrip
  { hPre :: Cond
  , hProg :: Prog
  , hPost :: Cond
  } deriving (Show)

data HETrip = HETrip
  { hePre :: Cond
  , heProg :: Prog
  , hePost :: Cond
  } deriving (Show)

data RHLETrip = RHLETrip
  { rhlePre :: Cond
  , rhleProgA :: Prog
  , rhleProgE :: Prog
  , rhlePost :: Cond
  } deriving (Show)

hVcs :: HTrip -> Cond
hVcs (HTrip pre prog post) = impl pre (hWp prog post)

heVcs :: HETrip -> Cond
heVcs (HETrip pre prog post) = impl pre (heWp prog post)

rhleVcs :: RHLETrip -> Cond
rhleVcs (RHLETrip pre progA progE post) = BTrue

hWp :: Stmt -> Cond -> Cond
hWp stmt post =
  case stmt of
    Skip        -> post
    Seq []      -> post
    Seq (s:ss)  -> hWp s (hWp (Seq ss) post)
    Call func   -> BAnd (impl (postCond func) post)
                        (preCond func)
    var := aexp -> bsubst post var aexp
    If c s1 s2  -> BAnd (impl c (hWp s1 post))
                        (impl (BNot c) (hWp s2 post))

heWp :: Stmt -> Cond -> Cond
heWp stmt post =
  case stmt of
  Call func -> BAnd (impl post (postCond func))
                    (preCond func)
  -- TODO: The following corresponds to the ELift rule,
  -- which also says the program must have at least one
  -- terminating state.
  _ -> hWp stmt post

condToZ3 :: Cond -> Z3 AST
condToZ3 cond =
  case cond of
    BTrue -> mkTrue
    BFalse -> mkFalse
    aexp1 :=: aexp2 -> do
      z3Exp1 <- aexpToZ3 aexp1
      z3Exp2 <- aexpToZ3 aexp2
      mkEq z3Exp1 z3Exp2
    BNot bexp -> condToZ3 bexp >>= mkNot
    BAnd bexp1 bexp2 -> do
      z3Exp1 <- condToZ3 bexp1
      z3Exp2 <- condToZ3 bexp2
      mkAnd [z3Exp1, z3Exp2]

aexpToZ3 :: AExp -> Z3 AST
aexpToZ3 aexp =
  case aexp of
    I i -> mkIntNum i
    V var -> mkStringSymbol var >>= mkIntVar
    aexp1 :+: aexp2 -> aexpBinopToZ3 mkAdd aexp1 aexp2
    aexp1 :-: aexp2 -> aexpBinopToZ3 mkSub aexp1 aexp2
    aexp1 :*: aexp2 -> aexpBinopToZ3 mkMul aexp1 aexp2

aexpBinopToZ3 :: ([AST] -> Z3 AST) -> AExp -> AExp -> Z3 AST
aexpBinopToZ3 f aexp1 aexp2 = do
  lhs <- aexpToZ3 aexp1
  rhs <- aexpToZ3 aexp2
  f [lhs, rhs]

-------------------------------------
-- Useful for REPL experimentation --
-------------------------------------
func1 = UFunc "f1" ((V "x") :=: (I 0)) ((V "z") :=: (I 3))
func2 = UFunc "f2" BTrue ((V "z") :=: ((V "x") :+: (I 3)))
funcRand = UFunc "rand" BTrue BTrue
prog1 = Seq ["x" := (I 0), "y" := (I 0), Call func2]
prog2 = Seq ["x" := (I 0), "y" := (I 0), Call funcRand]
cond1 = (V "z") :=: (I 3)
htrip1 = HTrip BTrue prog1 cond1
htrip2 = HTrip BTrue prog2 cond1
hetrip1 = HETrip BTrue prog1 cond1
hetrip2 = HETrip BTrue prog2 cond1

printZ3 :: Cond -> IO String
printZ3 cond = evalZ3 (condToZ3 cond >>= astToString)
