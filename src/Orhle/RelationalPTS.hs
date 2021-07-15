module Orhle.RelationalPTS
  ( relBackwardPT
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import qualified Ceili.InvariantInference.Pie as Pie
import Orhle.SpecImp
import Orhle.StepStrategy


relBackwardPT :: BackwardStepStrategy
               -> SpecImpEnv
               -> [SpecImpProgram]
               -> [SpecImpProgram]
               -> Assertion
               -> Ceili Assertion
relBackwardPT stepStrategy env aprogs eprogs post = do
  Step selection aprogs' eprogs' <- stepStrategy aprogs eprogs
  case selection of
    UniversalStatement stmt -> do
      post' <- impBackwardPT (SIQ_Universal, env) stmt post
      relBackwardPT stepStrategy env aprogs' eprogs' post'
    ExistentialStatement stmt -> do
      post' <- impBackwardPT (SIQ_Existential, env) stmt post
      relBackwardPT stepStrategy env aprogs' eprogs' post'
    LoopFusion aloops eloops -> do
      error "unimplemented"
    NoSelectionFound -> case (aprogs', eprogs') of
                          ([], []) -> return post
                          _ -> throwError "Unable to find step"
