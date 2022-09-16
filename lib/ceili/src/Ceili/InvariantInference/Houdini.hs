{-# LANGUAGE FlexibleContexts #-}

-- Loop invariance inspired by Houdini.
-- "Houdini, an annotation assistant for ESC/Java."
-- Flanagan, Cormac, and K. Rustan M. Leino
-- International Symposium of Formal Methods Europe.
-- Springer, Berlin, Heidelberg, 2001.

module Ceili.InvariantInference.Houdini
  ( Embeddable(..)
  , infer
  ) where

import Ceili.Assertion ( Assertion(..) )
import Ceili.CeiliEnv
import Ceili.FeatureLearning.LinearInequalities
import Ceili.Name
import qualified Ceili.SMT as SMT
import Control.Monad ( filterM )
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter

infer :: ( Embeddable Integer t
         , SMT.ValidCheckable t
         , Pretty t
         , Eq t
         , Ord t
         )
      => Set Name
      -> Set t
      -> Int
      -> Assertion t
      -> (Assertion t -> Ceili (Assertion t))
      -> Ceili (Assertion t)
infer names lits size precond computeSP = do
  log_i "[Houdini] Beginning invariant inference with Houdini"
  log_d $ (show $ Set.size names) ++ " names, "
       ++ (show $ Set.size lits) ++ " lits"
  candidates <- findCandidates names lits size precond
  log_d $ "[Houdini] Filtered candidates: " ++ (show $ length candidates)
  inductiveClauses <- houdini candidates computeSP
  log_i $ "[Houdini] Invariant: " ++ (show $ And inductiveClauses)
  return $ And inductiveClauses

findCandidates :: ( Embeddable Integer t
                  , SMT.ValidCheckable t
                  , Ord t
                  , Eq t)
               => Set Name
               -> Set t
               -> Int
               -> Assertion t
               -> Ceili [Assertion t]
findCandidates names lits size precond = do
  let candidates = linearInequalities lits names size
  log_d $ "[Houdini] Initial candidate size: " ++ (show $ Set.size candidates)
  filterM (checkValidB . Imp precond) $ Set.toList candidates

houdini :: SMT.ValidCheckable t
        => [Assertion t]
        -> (Assertion t -> Ceili (Assertion t))
        -> Ceili [Assertion t]
houdini candidates computeSP = do
  log_i $ "[Houdini] Starting pass with "
    ++ (show $ length candidates)
    ++ " candidate clauses."
  sp <- computeSP $ And candidates
  let isValid candidate = do
        valid <- checkValidWithLog LogLevelNone $ Imp sp candidate
        return $ case valid of
          SMT.Valid -> True
          _         -> False
  inductive <- filterM isValid candidates
  if (length inductive == length candidates)
    then return candidates
    else houdini inductive computeSP
