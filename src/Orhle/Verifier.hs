module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , rhleVerifier
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Name
import qualified Ceili.SMT as SMT
import qualified Data.Set as Set
import Orhle.RelationalPTS
import Orhle.SpecImp
import Orhle.StepStrategy
import Orhle.Triple

data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: SpecImpEnv SpecImpProgram -> RhleTriple -> IO (Either Failure Success)
rhleVerifier funEnv triple@(RhleTriple pre aprogs eprogs post) = do
  wpResult <- runCeili (mkEnv $ TripleWithFunEnv funEnv triple) $
              relBackwardPT backwardWithFusion funEnv aprogs eprogs post
  case wpResult of
    Left msg  -> return $ Left $ Failure msg
    Right wp -> do
      result <- SMT.checkValid $ Imp pre wp
      return $ case result of
        SMT.Valid         -> Right $ Success
        SMT.Invalid model -> Left  $ Failure $ "Verification conditions are invalid. Model: " ++ model
        SMT.ValidUnknown  -> Left  $ Failure "Solver returned unknown."

data TripleWithFunEnv e = TripleWithFunEnv (SpecImpEnv e) RhleTriple
instance CollectableNames e => CollectableNames (TripleWithFunEnv e) where
  namesIn (TripleWithFunEnv funEnv trip) = Set.union (namesIn funEnv) (namesIn trip)
