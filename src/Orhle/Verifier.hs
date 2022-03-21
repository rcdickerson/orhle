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
import Ceili.Literal
import Ceili.Name
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Control.Monad.Trans ( lift )
import Data.List ( isSuffixOf )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Orhle.CValue
import Orhle.RelationalPTS
import Orhle.SpecImp
import Orhle.StepStrategy
import Orhle.Triple
import System.Random

data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: SpecImpEnv Integer (SpecImpProgram Integer)
             -> RhleTriple Integer
             -> IO (Either Failure Success)
rhleVerifier iFunEnv triple = do
  let pre = (fmap Concrete) . rhlePre $ triple
  let post = (fmap Concrete) . rhlePost $ triple
  let prepareProg = (populateLoopIds @(SpecImpProgram CValue) @CValue)
                  . (mapImpType Concrete)
  aprogs  <- mapM prepareProg $ rhleAProgs triple
  eprogs  <- mapM prepareProg $ rhleEProgs triple
  let cFunEnv = mapSpecImpEnvType Concrete iFunEnv
  let names = Set.union (namesIn aprogs) (namesIn eprogs)
  let lits  = Set.union (litsIn  aprogs) (litsIn eprogs)
  let env = mkEnv LogLevelDebug 5000 names
  resultOrErr <- runCeili env $ do
    log_i $ "Collecting loop head states for loop invariant inference..."
    aLoopHeads <- mapM (headStates 5 cFunEnv) aprogs
    eLoopHeads <- mapM (headStates 5 cFunEnv) eprogs
    let loopHeads = Map.unions $ aLoopHeads ++ eLoopHeads
    -- log_d $ "Loop heads: " ++ show loopHeads
    log_i $ "Running backward relational analysis..."
    let namesNoRets = Set.filter (\(Name name _) -> not $ "!retVal" `isSuffixOf` name) names
    let ptsContext = RelSpecImpPTSContext cFunEnv loopHeads namesNoRets lits
    wp <- relBackwardPT backwardWithFusion ptsContext aprogs eprogs post
    checkValid $ Imp pre wp
  case resultOrErr of
    Left msg  -> pure . Left . Failure $ msg
    Right result -> do
      return $ case result of
        SMT.Valid         -> Right $ Success
        SMT.Invalid model -> Left  $ Failure $ "Verification conditions are invalid. Model: " ++ model
        SMT.ValidUnknown  -> Left  $ Failure "Solver returned unknown."

headStates :: Int
           -> SpecImpEnv CValue (SpecImpProgram CValue)
           -> SpecImpProgram CValue
           -> Ceili (LoopHeadStates CValue)
headStates numRandomStates env prog = do
  let ctx = SpecImpEvalContext (Fuel 10) env
  let names = Set.toList $ namesIn prog
  randomStates <- sequence . take numRandomStates . repeat $ randomState names
  let sts = [ Map.fromList $ map (\n -> (n, Concrete 1)) names
            , Map.fromList $ map (\n -> (n, Concrete 0))  names
            , Map.fromList $ map (\n -> (n, Concrete $ -1))  names ]
            ++ randomStates
  collectLoopHeadStates ctx sts prog

randomState :: [Name] -> Ceili (ProgState CValue)
randomState names = do
  g <- lift . lift $ newStdGen
  let values = map Concrete $ take (length names) (randomRs (-1000, 1000) g :: [Integer])
  pure $ Map.fromList $ zip names values
