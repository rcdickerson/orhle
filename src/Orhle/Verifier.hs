module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , rhleVerifier
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import qualified Ceili.SMT as SMT
import Orhle.RelationalPTS
import Orhle.SpecImp
import Orhle.StepStrategy
import Orhle.Triple

data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: SpecImpEnv SpecImpProgram -> RhleTriple -> IO (Either Failure Success)
rhleVerifier specs triple@(RhleTriple pre aprogs eprogs post) = do
  wpResult <- runCeili (mkEnv triple) $
              relBackwardPT backwardWithFusion specs aprogs eprogs post
  case wpResult of
    Left msg  -> return $ Left $ Failure msg
    Right wp -> do
      result <- SMT.checkValid $ Imp wp pre
      return $ case result of
        SMT.Valid         -> Right $ Success
        SMT.Invalid model -> Left  $ Failure $ "Verification conditions are invalid. Model: " ++ model
        SMT.ValidUnknown  -> Left  $ Failure "Solver returned unknown."
