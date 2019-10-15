-- https://theory.stanford.edu/~aiken/publications/papers/cav12b.pdf

module MSA
  ( findMsaVars
  , findMusVars
  ) where

import qualified Data.Set as Set
import Z3.Monad
import Z3Util

findMsaVars :: AST -> [Symbol] -> Z3 [Symbol]
findMsaVars formula vars = do
  musVars <- findMusVarSet formula varSet 0
  return $ Set.toList $ Set.difference varSet musVars
  where
    varSet = Set.fromList vars

findMusVars :: AST -> [Symbol] -> Z3 [Symbol]
findMusVars formula vars = do
  musVars <- findMusVarSet formula (Set.fromList vars) 0
  return $ Set.toList musVars

findMusVarSet :: AST -> Set.Set Symbol -> Int -> Z3 (Set.Set Symbol)
findMusVarSet formula candidateVars lowerBound = do
  if (null candidateVars) || (length candidateVars) <= lowerBound
    then return Set.empty
    else do
      let best = Set.empty
      let (var, candidateVars') = chooseFrom candidateVars
      varApp   <- toApp =<< mkIntVar var
      formula' <- mkForallConst [] [varApp] formula
      isSat    <- checkSat formula'
      best' <- if isSat
        then do
          y <- findMusVarSet formula' candidateVars' $ lowerBound - 1
          let cost = (length y) + 1
          if (cost > lowerBound)
            then return $ Set.insert var y
            else return   best
        else return best
      y' <- findMusVarSet formula candidateVars' lowerBound
      return $ if (length y') > lowerBound then y' else best'

chooseFrom :: Set.Set Symbol -> (Symbol, Set.Set Symbol)
chooseFrom = Set.deleteFindMin
