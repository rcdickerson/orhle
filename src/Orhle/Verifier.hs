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
import Orhle.CState
import Orhle.RelationalPTS
import Orhle.SpecImp
import Orhle.StepStrategy
import Orhle.Triple
import Prettyprinter

data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: SpecImpEnv Integer (SpecImpProgram Integer)
             -> RhleTriple Integer
             -> IO (Either Failure Success)
rhleVerifier iFunEnv triple = do
  let pre = (fmap Concrete) . rhlePre $ triple
  let ppost = (fmap Concrete) . rhlePost $ triple
  aprogs <- populateLoopIds . (mapImpType Concrete) $ rhleAProgs triple
  eprogs <- populateLoopIds . (mapImpType Concrete) $ rhleEProgs triple
  let sFunEnv = mapSpecImpEnvType Concrete iFunEnv
  let names = Set.union (namesIn aprogs) (namesIn eprogs)
  let lits  = Set.union (litsIn  aprogs) (litsIn  eprogs)
  let env = mkEnv LogLevelInfo 2000 names
  wpResult <- runCeili env $ do
    log_i $ "Collecting loop head states for loop invariant inference..."
    aLoopHeads <- mapM (headStates sFunEnv) aprogs
    eLoopHeads <- mapM (headStates sFunEnv) eprogs
    let loopHeads = Map.unions $ aLoopHeads ++ eLoopHeads
    log_i $ "Running backward relational analysis..."
    let ptsContext = RelSpecImpPTSContext sFunEnv loopHeads names lits
    relBackwardPT backwardWithFusion ptsContext aprogs eprogs post
  case wpResult of
    Left msg  -> return $ Left $ Failure msg
    Right wp -> do
      result <- SMT.checkValid $ Imp pre wp
      return $ case result of
        SMT.Valid         -> Right $ Success
        SMT.Invalid model -> Left  $ Failure $ "Verification conditions are invalid. Model: " ++ model
        SMT.ValidUnknown  -> Left  $ Failure "Solver returned unknown."

headStates :: SpecImpEnv CValue (SpecImpProgram CValue)
           -> SpecImpProgram CValue
           -> Ceili (LoopHeadStates CValue)
headStates env prog = do
  let ctx = SpecImpEvalContext (Fuel 100) env
  let names = Set.toList $ namesIn prog
  let sts = [ Map.fromList $ map (\n -> (n, -1)) names
            , Map.fromList $ map (\n -> (n, 0))  names
            , Map.fromList $ map (\n -> (n, 1))  names ]
  collectLoopHeadStates ctx sts prog
