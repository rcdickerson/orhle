module Orhle.VerifierEnv
  ( Env(..)
  , Verification
  , buildEnv
  , envAddChoiceVar
  , envAddChoiceVars
  , envFork
  , envFreshen
  , envGetDefaultInvarFilter
  , envGetQuant
  , envLog
  , envSetDefaultInvarFilter
  , envSetQuant
  , envWithChoice
  , runVerificationTask
  , throwError
  ) where

import           Ceili.Assertion ( Assertion(..) )
import qualified Ceili.Assertion as A
import           Ceili.Name
import           Control.Monad.IO.Class ( liftIO )
import           Control.Monad.Except ( ExceptT, runExceptT, throwError )
import           Control.Monad.Trans.State
import           Data.Set  ( Set )
import qualified Data.Set as Set
import           Orhle.SpecImp
import           Orhle.Triple
import           System.IO ( hFlush, stdout )

data Env = Env { env_quant              :: SpecImpQuant
               , env_specs              :: SpecImpEnv
               , env_freshMap           :: NextFreshIds
               , env_choiceVars         :: Set TypedName
               , env_defaultInvarFilter :: Assertion
               } -- TODO: Optics

type Verification a = StateT Env (ExceptT String IO) a

runVerificationTask :: Env -> Verification a -> IO (Either String a)
runVerificationTask task env = runExceptT (evalStateT env task)

-- runBackwardAnalysis :: Env -> RhleTriple -> IO (Either String Assertion)
-- runBackwardAnalysis env triple =
--   let task = envImpWithChoice =<< (env_bStepStrat env $ reverseTriple triple)
--   in runVerificationTask env task

-- runForwardAnalysis :: Env -> RhleTriple -> IO (Either String Assertion)
-- runForwardAnalysis env triple =
--   let task = envImpWithChoice =<< (env_fStepStrat env $ triple)
--   in runVerificationTask env task

buildEnv :: SpecImpEnv
         -> RhleTriple
         -> Env
buildEnv specs (RhleTriple pre aprogs eprogs post) =
  Env SIQ_Universal specs freshMap Set.empty A.ATrue
  where
    names = Set.unions [ namesIn pre
                       , Set.unions $ map namesIn aprogs
                       , Set.unions $ map namesIn eprogs
                       , namesIn post
                       , namesIn specs
                       ]
    freshMap = buildFreshIds names

envFork :: Verification Env
envFork = do
  Env quant specs freshMap cvars dif <- get
  return $ Env quant specs freshMap cvars dif

envFreshen :: FreshableNames a => a -> Verification a
envFreshen name = do
  Env quant specs freshMap cvars dif <- get
  let (freshMap', freshName) = runFreshen freshMap name
  put $ Env quant specs freshMap' cvars dif
  return freshName

envSetQuant :: SpecImpQuant -> Verification ()
envSetQuant quant = do
  Env _ specs freshMap cvars dif <- get
  put $ Env quant specs freshMap cvars dif

envGetQuant :: Verification SpecImpQuant
envGetQuant = get >>= return . env_quant

envAddChoiceVar :: TypedName -> Verification ()
envAddChoiceVar var = do
  Env quant specs freshMap cvars dif <- get
  let cvars' = Set.insert var cvars
  put $ Env quant specs freshMap cvars' dif

envAddChoiceVars :: [TypedName] -> Verification ()
envAddChoiceVars vars = do
  Env quant specs freshMap cvars dif <- get
  let cvars' = foldr Set.insert cvars vars
  put $ Env quant specs freshMap cvars' dif

envWithChoice :: Assertion -> Verification Assertion
envWithChoice assertion = do
  cvars <- get >>= return . Set.toList . env_choiceVars
  return $ case length cvars of
             0 -> assertion
             _ -> Exists cvars $ assertion

envSetDefaultInvarFilter :: Assertion -> Verification ()
envSetDefaultInvarFilter dif = do
  Env quant specs freshMap cvars _ <- get
  put $ Env quant specs freshMap cvars dif

envGetDefaultInvarFilter :: Verification Assertion
envGetDefaultInvarFilter = get >>= return . env_defaultInvarFilter

envLog :: String -> Verification ()
envLog str = do
  -- Replacable with something fancier later.
  liftIO $ putStrLn str
  liftIO $ hFlush stdout
