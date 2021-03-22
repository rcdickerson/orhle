module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , Verifier
  , rhleVerifier
  ) where

import           Control.Monad ( foldM )
import           Control.Monad.Identity ( Identity, runIdentity )
import           Control.Monad.Trans.State
import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion )
import qualified Orhle.Assertion as A
import qualified Orhle.InvariantInference as Inf
import           Orhle.Imp.ImpLanguage ( Program(..), BExp )
import qualified Orhle.Imp.ImpLanguage as Imp
import           Orhle.Names  ( Name(..), NextFreshIds, namesIn )
import qualified Orhle.Names as Names
import           Orhle.Spec
import           Orhle.Triple

------------------------------
-- Verification Environment --
------------------------------

data VQuant = VUniversal
            | VExistential
            deriving Show

data Env = Env { env_quant    :: VQuant
               , env_specs    :: AESpecs
               , env_freshMap :: NextFreshIds
               }

buildEnv :: AESpecs -> RhleTriple -> Env
buildEnv specs (RhleTriple pre aProgs eProgs post) = Env VUniversal specs freshMap
  where
    allNames = [ namesIn pre
               , Set.unions $ map namesIn aProgs
               , Set.unions $ map namesIn eProgs
               , namesIn post
               , namesIn specs]
    freshMap = Names.buildNextFreshIds $ Set.unions allNames

type Verification a = StateT Env Identity a

envFreshen :: Traversable t => t Name -> Verification (t Name)
envFreshen names = do
  Env quant specs freshMap <- get
  let (freshX, freshMap') = Names.freshen names freshMap
  put $ Env quant specs freshMap'
  return freshX

envPutQSpecs :: VQuant -> SpecMap -> Verification ()
envPutQSpecs quant specs = do
  Env _ (AESpecs aspecs especs) freshMap <- get
  let aespecs = case quant of
                  VUniversal   -> AESpecs specs  especs
                  VExistential -> AESpecs aspecs specs
  put $ Env quant aespecs freshMap

envGetQSpecs :: Verification (VQuant, SpecMap)
envGetQSpecs = do
  Env quant (AESpecs aspecs especs) _ <- get
  let specs = case quant of
                VUniversal   -> aspecs
                VExistential -> especs
  return (quant, specs)


--------------
-- Verifier --
--------------

type Verifier = AESpecs -> RhleTriple -> IO (Either Failure Success)
data Failure  = Failure { failureVcs :: Assertion,  message :: String }
data Success  = Success { successVcs :: Assertion }

rhleVerifier :: Verifier
rhleVerifier specs (RhleTriple pre aProgs eProgs post) =
  let
    pnamesAsAriths = Set.fromList . namesToIntVars . Set.toList . namesIn
    plitsAsAriths  = (Set.map A.Num) . Imp.plits
    valsAtHole _ = Set.toList . Set.unions $
                   (map pnamesAsAriths (aProgs ++ eProgs)) ++
                   (map plitsAsAriths  (aProgs ++ eProgs))
    vcTransform filledAProgs filledEProgs = let
      triple = RhleTriple pre filledAProgs filledEProgs post
      in runIdentity $ evalStateT (buildVCs specs triple) (buildEnv specs triple)
  in do
    result <- Inf.inferAndCheck (Inf.Enumerative 2) valsAtHole vcTransform aProgs eProgs
    return $ case result of
      Left  msg -> Left  $ Failure (vcTransform aProgs eProgs) msg
      Right _   -> Right $ Success (vcTransform aProgs eProgs) -- TODO: filled VCs

buildVCs :: AESpecs -> RhleTriple -> Verification Assertion
buildVCs (AESpecs aspecs especs) (RhleTriple pre aProgs eProgs post) = do
    envPutQSpecs VExistential especs
    post'  <- foldM (flip weakestPre) post eProgs
    envPutQSpecs VUniversal aspecs
    post'' <- foldM (flip weakestPre) post' aProgs
    return $ A.Imp pre post''


------------------------------------
-- Weakest Precondition Semantics --
------------------------------------

weakestPre :: Program -> Assertion -> Verification Assertion
weakestPre stmt post =
  case stmt of
    SSkip             -> return post
    SSeq []           -> return post
    SSeq (s:ss)       -> weakestPre s =<< weakestPre (SSeq ss) post
    SAsgn lhs rhs     -> return $ A.subArith (A.Ident lhs A.Int) (Imp.aexpToArith rhs) post
    SIf b s1 s2       -> wpIf b s1 s2 post
    SWhile b body inv -> wpLoop b body inv post
    SCall f assignees -> wpCall f assignees post

wpIf :: BExp -> Program -> Program -> Assertion -> Verification Assertion
wpIf condB tBranch eBranch post = do
  wpT <- weakestPre tBranch post
  wpE <- weakestPre eBranch post
  let cond   = Imp.bexpToAssertion condB
      ncond  = A.Not $ cond
  return $ A.And [A.Imp cond wpT, A.Imp ncond wpE]

wpLoop :: BExp -> Program -> (Assertion, A.Arith) -> Assertion -> Verification Assertion
wpLoop condB body (inv, measure) post = do
  let cond    = Imp.bexpToAssertion condB
      varSet  = Set.unions [namesIn condB, namesIn body]
      vars    = Set.toList varSet
  freshVars  <- envFreshen vars
  let freshen = Names.substituteAll vars freshVars
  (quant, _) <- envGetQSpecs
  bodyWP     <- (case quant of
                   VUniversal   -> weakestPre body inv
                   VExistential -> let
                     nextMeasure = Names.substituteAll vars freshVars measure
                     measureCond = A.Lt measure nextMeasure
                     bodyPost    = A.And [inv, measureCond]
                     in weakestPre body bodyPost)
  let qIdents = namesToIntIdents freshVars
      loopWP  = A.Forall qIdents (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      endWP   = A.Forall qIdents (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
  return $ A.And [inv, loopWP, endWP]

wpCall :: Imp.SFun -> [Name] -> Assertion -> Verification Assertion
wpCall (Imp.SFun funName funParams) assignees post = do
  (quant, specs) <- envGetQSpecs
  case (specAtCallsite assignees funParams funName specs) of
    Nothing -> error $ "No " ++ (show quant) ++ " specification for " ++ show funName ++
               ". Specified functions are: " ++ (show $ funList specs)
    Just (cvars, fPre, fPost) ->
      case quant of
        VUniversal   -> return $ A.And [fPre, A.Imp fPost post]
        VExistential -> do
          frAssignees <- envFreshen assignees
          let freshen     = Names.substituteAll assignees frAssignees
              frPost      = freshen post
              frFPost     = freshen fPost
              frIdents    = (namesToIntIdents frAssignees)
              existsPost  = A.Exists frIdents frFPost
              forallPost  = A.Forall frIdents $ A.Imp frFPost frPost
              wp          = A.And [fPre, existsPost, forallPost]
          return $ case cvars of
            [] -> wp
            _  -> A.Exists cvars wp

namesToIntIdents :: Functor f => f Name -> f A.Ident
namesToIntIdents = fmap (\v -> A.Ident v A.Int)

namesToIntVars :: Functor f => f Name -> f A.Arith
namesToIntVars = (fmap A.Var) . namesToIntIdents
