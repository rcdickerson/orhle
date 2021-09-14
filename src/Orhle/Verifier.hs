{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , rhleVerifier
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Evaluation
import Ceili.Literal
import Ceili.Name
import qualified Ceili.SMT as SMT
import Ceili.SMTString
import Ceili.StatePredicate
import qualified Data.Map as Map
import qualified Data.Set as Set
import Orhle.RelationalPTS
import Orhle.SpecImp
import Orhle.StepStrategy
import Orhle.Triple
import Prettyprinter

data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: forall t.
                ( Num t
                , Ord t
                , SMTString t
                , SMTTypeString t
                , AssertionParseable t
                , Pretty t
                , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (AExp t) t
                , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (BExp t) Bool
                , StatePredicate (Assertion t) t
                ) => SpecImpEnv t (SpecImpProgram t) -> RhleTriple t -> IO (Either Failure Success)
rhleVerifier funEnv (RhleTriple pre aprogs eprogs post) = do
  let names = Set.union (namesIn aprogs) (namesIn eprogs)
  let lits  = Set.union (litsIn  aprogs) (litsIn  eprogs)
  let env = mkEnv LogLevelInfo 2000 names
  aprogsWithLoopIds <- mapM (populateLoopIds @(SpecImpProgram t) @t) aprogs
  eprogsWithLoopIds <- mapM (populateLoopIds @(SpecImpProgram t) @t) eprogs
  wpResult <- runCeili env $ do
    log_i $ "Collecting loop head states for loop invariant inference..."
    aLoopHeads <- mapM (headStates funEnv) aprogsWithLoopIds
    eLoopHeads <- mapM (headStates funEnv) eprogsWithLoopIds
    let loopHeads = Map.unions $ aLoopHeads ++ eLoopHeads
    log_i $ "Running backward relational analysis..."
    let ptsContext = RelSpecImpPTSContext funEnv loopHeads names lits
    relBackwardPT backwardWithFusion ptsContext aprogsWithLoopIds eprogsWithLoopIds post
  case wpResult of
    Left msg  -> return $ Left $ Failure msg
    Right wp -> do
      result <- SMT.checkValid $ Imp pre wp
      return $ case result of
        SMT.Valid         -> Right $ Success
        SMT.Invalid model -> Left  $ Failure $ "Verification conditions are invalid. Model: " ++ model
        SMT.ValidUnknown  -> Left  $ Failure "Solver returned unknown."

headStates :: ( Num t
              , Ord t
              , SMTString t
              , SMTTypeString t
              , AssertionParseable t
              , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (AExp t) t
              , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (BExp t) Bool
              ) => SpecImpEnv t (SpecImpProgram t) -> SpecImpProgram t -> Ceili (LoopHeadStates t)
headStates env prog = do
  let ctx = SpecImpEvalContext (Fuel 100) env
  let names = Set.toList $ namesIn prog
  let sts = [ Map.fromList $ map (\n -> (n, -1)) names
            , Map.fromList $ map (\n -> (n, 0))  names
            , Map.fromList $ map (\n -> (n, 1))  names ]
  collectLoopHeadStates ctx sts prog
