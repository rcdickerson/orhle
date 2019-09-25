-- https://theory.stanford.edu/~aiken/publications/papers/cav12b.pdf

module MSA
  ( findMsaVars
  , findMusVars
  ) where

import qualified Data.Set as Set
import Z3.Monad
import Z3Util

import Debug.Trace

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
  formulaStr <- astToString formula
  traceM $ "Finding MUS set for " ++ formulaStr
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


{-
  formulaStr <- astToString formula
  candidateVarStrs <- sequence $ map getSymbolString $ Set.toList candidateVars
  traceM $ "findMusVarSet " ++ formulaStr ++ " " ++ (show candidateVarStrs) ++ " " ++ (show lowerBound)
  if (length candidateVars) <= lowerBound
    then return Set.empty
    else case (chooseFrom candidateVars) of
      Nothing -> return Set.empty
      Just (var, varBar) -> findMusVarSet' formula var varBar lowerBound

findMusVarSet' :: AST -> Symbol -> Set.Set Symbol -> Int -> Z3 (Set.Set Symbol)
findMusVarSet' formula var varBar lowerBound = do
  varApp   <- toApp =<< mkIntVar var
  formula' <- mkForallConst [] [varApp] formula
  formula'Str <- astToString formula'
  traceM $ "checking SAT of: " ++ formula'Str
  isSat <- checkSat formula'
  (mus, lowerBound') <- step formula' isSat
  traceM $ "Done checking SAT: " ++ (show isSat)
  mus' <- findMusVarSet formula varBar lowerBound'
  return $ if (length mus') > lowerBound' then mus' else mus
  where
    step _        False = return (Set.empty, lowerBound)
    step formula' True  = do
      mus <- findMusVarSet formula' varBar $ lowerBound - 1
      let cost = (length mus) + 1
      traceM $ "New cost: " ++ (show cost)
      return $ if cost > lowerBound
        then (Set.insert var mus, cost)
        else (Set.empty, lowerBound)
-}

chooseFrom :: Set.Set Symbol -> (Symbol, Set.Set Symbol)
chooseFrom = Set.deleteFindMin
