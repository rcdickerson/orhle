-- https://theory.stanford.edu/~aiken/publications/papers/cav12b.pdf

module Orhle.Abduction.MSA
  ( findMsaVars
  , findMusVars
  ) where

import qualified Data.Set as Set
import Orhle.Assertion
import qualified Orhle.SMT as SMT

findMsaVars :: Assertion -> [Ident] -> IO [Ident]
findMsaVars formula vars = do
  musVars <- findMusVarSet formula varSet 0
  return $ Set.toList $ Set.difference varSet musVars
  where
    varSet = Set.fromList vars

findMusVars :: Assertion -> [Ident] -> IO [Ident]
findMusVars formula vars = do
  musVars <- findMusVarSet formula (Set.fromList vars) 0
  return $ Set.toList musVars

findMusVarSet :: Assertion -> Set.Set Ident -> Int -> IO (Set.Set Ident)
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

chooseFrom :: Set.Set Ident -> (Ident, Set.Set Ident)
chooseFrom = Set.deleteFindMin
