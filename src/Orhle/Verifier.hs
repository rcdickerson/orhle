{-# LANGUAGE FlexibleInstances #-}

module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , rhleVerifier
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Name
import qualified Ceili.SMT as SMT
import Control.Monad ( mapM )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Orhle.RelationalPTS
import Orhle.SpecImp
import Orhle.StepStrategy
import Orhle.Triple

data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: SpecImpEnv SpecImpProgram -> RhleTriple -> IO (Either Failure Success)
rhleVerifier funEnv triple@(RhleTriple pre aprogs eprogs post) = do
  let env = mkEnv LogLevelInfo
                  (TripleWithEnv (funEnv, triple))
                  2000
  wpResult <- runCeili env $ do
--    log_i $ "Populating test states for loop invariant inference..."
    aprogsWithTests <- return aprogs --mapM (withTestStates funEnv) aprogs
    eprogsWithTests <- return eprogs --mapM (withTestStates funEnv) eprogs
    log_i $ "Running backward relational analysis..."
    relBackwardPT backwardWithFusion funEnv aprogsWithTests eprogsWithTests post
  case wpResult of
    Left msg  -> return $ Left $ Failure msg
    Right wp -> do
      result <- SMT.checkValid $ Imp pre wp
      return $ case result of
        SMT.Valid         -> Right $ Success
        SMT.Invalid model -> Left  $ Failure $ "Verification conditions are invalid. Model: " ++ model
        SMT.ValidUnknown  -> Left  $ Failure "Solver returned unknown."

newtype TripleWithEnv e = TripleWithEnv (SpecImpEnv e, RhleTriple)
instance CollectableNames e => CollectableNames (TripleWithEnv e) where
  namesIn (TripleWithEnv (funEnv, trip)) = Set.union (namesIn funEnv) (namesIn trip)

withTestStates :: SpecImpEnv SpecImpProgram -> SpecImpProgram -> Ceili SpecImpProgram
withTestStates env prog = do
  let ctx = SpecImpEvalContext (Fuel 100) env
  let names = Set.toList $ namesIn prog
  let sts = [ Map.fromList $ map (\n -> (n, -1)) names
            , Map.fromList $ map (\n -> (n, 0))  names
            , Map.fromList $ map (\n -> (n, 1))  names ]
  populateTestStates ctx sts prog
