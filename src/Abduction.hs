module Abduction
    ( abduce
    , Abducible(..)
    , Abduction
    ) where

import Conditions
import Imp
import Z3.Monad

abduce :: Abduction -> Z3 AST
abduce ([], _, _) = mkTrue -- TODO: probably incorrect
abduce (duc : [], conds, post) = singleAbduction duc (conjoin conds) post
abduce _ = error "Multi-abduction is currently unsupported!"

singleAbduction :: Abducible -> Cond -> Cond -> Z3 AST
singleAbduction duc conds post = do
--  let imp  = CImp (CAnd conds (bexpToCond.postCond.func $ duc)) post
  let imp  = CImp conds (CAnd (bexpToCond.postCond.func $ duc) post)
  let vars = cvars imp
  let vbar = filter (\v -> not $ elem v (fParams.func $ duc)) vars
  condToZ3 imp >>= performQe vbar

performQe :: [Var] -> AST -> Z3 AST
performQe vars formula = do
  varSymbols <- mapM mkStringSymbol vars
  intVars <- mapM mkIntVar varSymbols
  appVars <- mapM toApp intVars
  qf <- mkForallConst [] appVars formula
  goal <- mkGoal False False False
  goalAssert goal qf
  qe <- mkTactic "qe"
  qeResult <- applyTactic qe goal
  subgoals <- getApplyResultSubgoals qeResult
  formulas <- mapM getGoalFormulas subgoals
  mkAnd $ concat formulas

data Abducible = Abducible
  { func :: UFunc } deriving (Show)

type Abduction = ([Abducible], [Cond], Cond)
