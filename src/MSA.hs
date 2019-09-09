-- https://theory.stanford.edu/~aiken/publications/papers/cav12b.pdf

module MSA
  ( findMsaVars
  ) where

import qualified Data.Set as Set
import Z3.Monad
import Z3Util

findMsaVars :: AST -> [Symbol] -> Z3 [Symbol]
findMsaVars formula vars = do
  musVars <- findMusVars formula varSet 0
  return $ Set.toList $ Set.difference varSet musVars
  where
    varSet = Set.fromList vars

findMusVars :: AST -> Set.Set Symbol -> Int -> Z3 (Set.Set Symbol)
findMusVars formula candidateVars lowerBound =
  if (length candidateVars) <= lowerBound
    then return Set.empty
    else case (chooseFrom candidateVars) of
      Nothing -> return Set.empty
      Just (var, varBar) -> findMusVars' formula var varBar lowerBound

findMusVars' :: AST -> Symbol -> Set.Set Symbol -> Int -> Z3 (Set.Set Symbol)
findMusVars' formula var varBar lowerBound = do
  varApp   <- toApp =<< mkIntVar var
  formula' <- mkForallConst [] [varApp] formula
  (mus, lowerBound') <- step formula' =<< checkSat formula'
  mus' <- findMusVars formula varBar lowerBound'
  return $ if (length mus') > lowerBound' then mus' else mus
  where
    step _        False = return (Set.empty, lowerBound)
    step formula' True  = do
      mus <- findMusVars formula' varBar $ lowerBound - 1
      let cost = (length mus) + 1
      return $ if cost > lowerBound
        then (Set.insert var mus, cost)
        else (Set.empty, lowerBound)

chooseFrom :: Set.Set Symbol -> Maybe (Symbol, Set.Set Symbol)
chooseFrom symbols = do
  minElt <- Set.lookupMin symbols
  return (minElt, Set.delete minElt symbols)
