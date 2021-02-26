-- https://theory.stanford.edu/~aiken/publications/papers/cav12b.pdf

module Orhle.Abduction.MSA
  ( findMsaVars
  , findMusVars
  ) where

import qualified Data.Set as Set
import           Orhle.SMT  ( SMT )
import qualified Orhle.SMT as SMT

findMsaVars :: SMT.Expr -> [SMT.Symbol] -> SMT [SMT.Symbol]
findMsaVars formula vars = do
  musVars <- findMusVarSet formula varSet 0
  return $ Set.toList $ Set.difference varSet musVars
  where
    varSet = Set.fromList vars

findMusVars :: SMT.Expr -> [SMT.Symbol] -> SMT [SMT.Symbol]
findMusVars formula vars = do
  musVars <- findMusVarSet formula (Set.fromList vars) 0
  return $ Set.toList musVars

findMusVarSet :: SMT.Expr -> Set.Set SMT.Symbol -> Int -> SMT (Set.Set SMT.Symbol)
findMusVarSet formula candidateVars lowerBound = do
  return Set.empty
  -- if (null candidateVars) || (length candidateVars) <= lowerBound
  --   then return Set.empty
  --   else do
  --     let best = Set.empty
  --     let (var, candidateVars') = chooseFrom candidateVars
  --     varApp     <- toApp =<< mkIntVar var
  --     formula'   <- mkForallConst [] [varApp] formula
  --     (isSat, _) <- checkSat formula'
  --     best' <- if isSat
  --       then do
  --         y <- findMusVarSet formula' candidateVars' $ lowerBound - 1
  --         let cost = (length y) + 1
  --         if (cost > lowerBound)
  --           then return $ Set.insert var y
  --           else return   best
  --       else return best
  --     y' <- findMusVarSet formula candidateVars' lowerBound
  --     return $ if (length y') > lowerBound then y' else best'

chooseFrom :: Set.Set SMT.Symbol -> (SMT.Symbol, Set.Set SMT.Symbol)
chooseFrom = Set.deleteFindMin
