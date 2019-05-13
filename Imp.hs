module Imp where

infix 1 :=
infix 2 :=:
infixl 6 :+:, :-:
infixl 7 :*:

type Var = String

data AExp
  = I Int
  | V Var
  | AExp :+: AExp
  | AExp :-: AExp
  | AExp :*: AExp
  deriving (Show)

data BExp
  = BTrue
  | BFalse
  | AExp :=: AExp
  | BNot BExp
  | BAnd BExp BExp
  deriving (Show)

bor :: BExp -> BExp -> BExp
bor bexp1 bexp2 = bsimpl $ BNot $ BAnd (BNot bexp1) (BNot bexp2)

impl :: BExp -> BExp -> BExp
impl bexp1 bexp2 = bsimpl $ bor (BNot bexp1) bexp2

bsimpl :: BExp -> BExp
bsimpl (BNot (BNot bexp)) = bexp
bsimpl (BNot bexp) = BNot (bsimpl bexp)
bsimpl (BAnd bexp1 bexp2) = BAnd (bsimpl bexp1) (bsimpl bexp2)
bsimpl bexp = bexp

data UFunc = UFunc
  { fName :: String
  , preCond :: BExp
  , postCond :: BExp
  } deriving (Show)

data Stmt
  = Skip
  | Var := AExp
  | Seq [Stmt]
  | If BExp Stmt Stmt
  | Call UFunc
  deriving (Show)

type Prog = Stmt

type State = [(Var, Int)]

asubst :: AExp -> Var -> AExp -> AExp
asubst aexp var repl =
  case aexp of
    I i -> I i
    V v -> if (v == var) then repl else aexp
    lhs :+: rhs -> (asubst lhs var repl) :+: (asubst rhs var repl)
    lhs :-: rhs -> (asubst lhs var repl) :-: (asubst rhs var repl)
    lhs :*: rhs -> (asubst lhs var repl) :*: (asubst rhs var repl)

bsubst :: BExp -> Var -> AExp -> BExp
bsubst bexp var aexp =
  case bexp of
    lhs :=: rhs -> (asubst lhs var aexp) :=: (asubst rhs var aexp)
    BNot b -> BNot (bsubst b var aexp)
    BAnd b1 b2 -> BAnd (bsubst b1 var aexp) (bsubst b2 var aexp)
    _ -> bexp
