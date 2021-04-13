module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , rhleVerifier
  ) where

import           Data.Either ( partitionEithers )
import           Data.List ( partition )
import           Orhle.Assertion
import           Orhle.Imp
import           Orhle.Inliner ( inline )
import qualified Orhle.PredTransSingle as PTS
import qualified Orhle.SMT as SMT
import           Orhle.Spec ( AESpecs(..) )
import qualified Orhle.StepStrategies as Step
import           Orhle.Triple
import           Orhle.VerifierEnv

data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: AESpecs -> FunImplEnv -> RhleTriple -> IO (Either Failure Success)
rhleVerifier specs impls (RhleTriple pre aProgs eProgs post) =
  case doInline impls aProgs eProgs of
    Left errs -> return . Left $ Failure $ "Problems inlining: " ++ show errs
    Right (inlineAs, inlineEs) -> do
      let triple = RhleTriple pre inlineAs inlineEs post
      let env = buildEnv specs
                         triple
                         Step.backwardWithFusion
                         Step.forwardWithFusion
      vcResult  <- runVerificationTask env $ do
                         dif <- computeDefaultInvarFilter triple
                         envSetDefaultInvarFilter dif
                         bStepStrat <- envBackwardStepStrat
                         (bStepStrat $ reverseTriple triple) >>= return . (uncurry Imp)
      case vcResult of
        Left msg  -> return $ Left $ Failure msg
        Right vcs -> do
          result <- SMT.checkValid True vcs
          return $ case result of
            SMT.Valid         -> Right $ Success
            SMT.Invalid model -> Left  $ Failure $ "Verification conditions are invalid. Model: " ++ model
            SMT.ValidUnknown  -> Left  $ Failure "Solver returned unknown."

doInline :: FunImplEnv -> [Program] -> [Program] -> Either [String] ([Program], [Program])
doInline impls aProgs eProgs = let
  inmap = partitionEithers . map (inline impls)
  (errorAs, inAs) = inmap aProgs
  (errorEs, inEs) = inmap eProgs
  in case (errorAs ++ errorEs) of
    []   -> Right (inAs, inEs)
    errs -> Left $ errs

-- Some invariant inference approaches require a precondition statement
-- to filter candidate clauses. However, forward program analysis is not
-- possible in general as we do not have a forward reasoning rule for
-- specified function calls. Here, we make a best effort at reasoning
-- forward as far as possible. While not a sound precondition filter
-- in general, this approach is sufficient to infer loop invariants in
-- simple cases. More complex programs require this precondition to be
-- annotated by the user, as this default may not be sufficient.
computeDefaultInvarFilter :: RhleTriple -> Verification Assertion
computeDefaultInvarFilter triple = let
  (RhleTriple pre aprogs eprogs post) = filterEmptyTrip triple
  stepHead (p:ps) q = do
    let (step, rest) = headProg p
    pre' <- PTS.strongestPostQ q step pre
    return $ if q == VUniversal
      then RhleTriple pre' (rest:ps) eprogs post
      else RhleTriple pre' aprogs (rest:ps) post
  splitSteppable = partition $ \p -> headIsLoop p || headIsCall p
  maybeStep progs q = case progs of
                        [] -> return Nothing
                        _  -> let (_, steppable) = splitSteppable progs
                              in if null steppable
                                 then return Nothing
                                 else (return . Just) =<< stepHead steppable q
  in do
    stepA <- maybeStep aprogs VUniversal
    stepE <- maybeStep eprogs VExistential
    case (stepA, stepE) of
      (Just triple', _) -> computeDefaultInvarFilter triple'
      (_, Just triple') -> computeDefaultInvarFilter triple'
      _                 -> return pre
