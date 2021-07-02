module Orhle.VerifierEnv
  ( Env(..)
  , BackwardStepStrategy
  , ForwardStepStrategy
  , Verification
  , VQuant(..)
  , buildEnv
  , envAddChoiceVar
  , envAddChoiceVars
  , envBackwardStepStrat
  , envFork
  , envForwardStepStrat
  , envFreshen
  , envGetDefaultInvarFilter
  , envGetQSpecs
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
import           Ceili.Name ( FreshableNames(..), Name(..), TypedName(..), NextFreshIds, namesIn )
import qualified Ceili.Name as Name
import           Control.Monad.IO.Class ( liftIO )
import           Control.Monad.Except ( ExceptT, runExceptT, throwError )
import           Control.Monad.Trans.State
import           Data.Set  ( Set )
import qualified Data.Set as Set
import           Orhle.Spec ( AESpecs(..), SpecMap )
import           Orhle.Triple
import           System.IO ( hFlush, stdout )

data VQuant = VUniversal
            | VExistential
            deriving (Eq, Ord, Show)

type ForwardStepStrategy  = RhleTriple -> Verification (Assertion, Assertion)
type BackwardStepStrategy = RhleTriple -> Verification (Assertion, Assertion)

data Env = Env { env_quant              :: VQuant
               , env_specs              :: AESpecs
               , env_freshMap           :: NextFreshIds
               , env_choiceVars         :: Set TypedName
               , env_bStepStrat         :: BackwardStepStrategy
               , env_fStepStrat         :: ForwardStepStrategy
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

buildEnv :: AESpecs
         -> RhleTriple
         -> BackwardStepStrategy
         -> ForwardStepStrategy
         -> Env
buildEnv specs (RhleTriple pre aprogs eprogs post) bStepStrat fStepStrat =
  Env VUniversal specs freshMap Set.empty bStepStrat fStepStrat A.ATrue
  where
    names = Set.unions [ namesIn pre
                       , Set.unions $ map namesIn aprogs
                       , Set.unions $ map namesIn eprogs
                       , namesIn post
                       , namesIn specs
                       ]
    freshMap = Name.buildFreshIds names

envFork :: Verification Env
envFork = do
  Env quant specs freshMap cvars bss fss dif <- get
  return $ Env quant specs freshMap cvars bss fss dif

envFreshen :: FreshableNames a => a -> Verification a
envFreshen name = do
  Env quant specs freshMap cvars bss fss dif <- get
  let (freshMap', freshName) = Name.runFreshen freshMap name
  put $ Env quant specs freshMap' cvars bss fss dif
  return freshName

envSetQuant :: VQuant -> Verification ()
envSetQuant quant = do
  Env _ specs freshMap cvars bss fss dif <- get
  put $ Env quant specs freshMap cvars bss fss dif

envGetQuant :: Verification VQuant
envGetQuant = get >>= return . env_quant

envGetQSpecs :: Verification (VQuant, SpecMap)
envGetQSpecs = do
  quant           <- get >>= return . env_quant
  (AESpecs as es) <- get >>= return . env_specs
  let specs = case quant of
                VUniversal   -> as
                VExistential -> es
  return (quant, specs)

envAddChoiceVar :: TypedName -> Verification ()
envAddChoiceVar var = do
  Env quant specs freshMap cvars bss fss dif <- get
  let cvars' = Set.insert var cvars
  put $ Env quant specs freshMap cvars' bss fss dif

envAddChoiceVars :: [TypedName] -> Verification ()
envAddChoiceVars vars = do
  Env quant specs freshMap cvars bss fss dif <- get
  let cvars' = foldr Set.insert cvars vars
  put $ Env quant specs freshMap cvars' bss fss dif

envImpWithChoice :: (Assertion, Assertion) -> Verification Assertion
envImpWithChoice (pre, post) = envWithChoice $ Imp pre post

envWithChoice :: Assertion -> Verification Assertion
envWithChoice assertion = do
  cvars <- get >>= return . Set.toList . env_choiceVars
  return $ case length cvars of
             0 -> assertion
             _ -> Exists cvars $ assertion

envForwardStepStrat :: Verification ForwardStepStrategy
envForwardStepStrat = get >>= return . env_fStepStrat

envBackwardStepStrat :: Verification BackwardStepStrategy
envBackwardStepStrat = get >>= return . env_bStepStrat

envSetDefaultInvarFilter :: Assertion -> Verification ()
envSetDefaultInvarFilter dif = do
  Env quant specs freshMap cvars bss fss _ <- get
  put $ Env quant specs freshMap cvars bss fss dif

envGetDefaultInvarFilter :: Verification Assertion
envGetDefaultInvarFilter = get >>= return . env_defaultInvarFilter

envLog :: String -> Verification ()
envLog str = do
  -- Replacable with something fancier later.
  liftIO $ putStrLn str
  liftIO $ hFlush stdout
