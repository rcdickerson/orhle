module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , Verifier
  , rhleVerifier
  ) where

import           Control.Monad ( foldM )
import           Control.Monad.Identity ( Identity, runIdentity )
import           Control.Monad.Trans.State
import           Data.Either ( partitionEithers )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion )
import qualified Orhle.Assertion as A
import qualified Orhle.InvariantInference as Inf
import           Orhle.Imp.ImpLanguage ( FunImplEnv, Program(..), BExp )
import qualified Orhle.Imp.ImpLanguage as Imp
import           Orhle.Inliner ( inline )
import           Orhle.Name  ( Name(..), NextFreshIds, TypedName(..), namesIn )
import qualified Orhle.Name as Name
import           Orhle.Spec ( AESpecs(..), Spec(..), SpecMap )
import qualified Orhle.Spec as Spec
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
    freshMap = Name.buildNextFreshIds $ Set.unions allNames

type Verification a = StateT Env Identity a

envFreshen :: Traversable t => t Name -> Verification (t Name)
envFreshen names = do
  Env quant specs freshMap <- get
  let (freshX, freshMap') = Name.freshen names freshMap
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

type Verifier = AESpecs -> FunImplEnv -> RhleTriple -> IO (Either Failure Success)
data Failure  = Failure { failureVcs :: Assertion,  message :: String }
data Success  = Success { successVcs :: Assertion }

rhleVerifier :: Verifier
rhleVerifier specs impls (RhleTriple pre aProgs eProgs post) =
  case doInline impls aProgs eProgs of
    Left errs -> return . Left $ Failure A.AFalse ("Problems inlining: " ++ show errs)
    Right (inlineAs, inlineEs) -> let
      pnamesAsAriths = Set.fromList . namesToIntVars . Set.toList . namesIn
      plitsAsAriths  = (Set.map A.Num) . Imp.plits
      valsAtHole _   = Set.toList . Set.unions $
                         (map pnamesAsAriths (inlineAs ++ inlineEs)) ++
                         (map plitsAsAriths  (inlineAs ++ inlineEs))
      vcTransform filledAs filledEs = runVCs specs $ RhleTriple pre filledAs filledEs post
      in do
        result <- Inf.inferAndCheck (Inf.Enumerative 2) valsAtHole vcTransform inlineAs inlineEs
        return $ case result of
          Left  msg -> Left  $ Failure (vcTransform inlineAs inlineEs) msg
          Right _   -> Right $ Success (vcTransform inlineAs inlineEs) -- TODO: filled VCs

doInline :: FunImplEnv -> [Program] -> [Program] -> Either [String] ([Program], [Program])
doInline impls aProgs eProgs = let
  inmap = partitionEithers . map (inline impls)
  (errorAs, inAs) = inmap aProgs
  (errorEs, inEs) = inmap eProgs
  in case (errorAs ++ errorEs) of
    []   -> Right (inAs, inEs)
    errs -> Left $ errs

runVCs :: AESpecs -> RhleTriple -> Assertion
runVCs specs triple = runIdentity $ evalStateT (buildVCs specs triple) (buildEnv specs triple)

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
    SAsgn lhs rhs     -> return $ A.subArith (TypedName lhs Name.Int)
                                             (Imp.aexpToArith rhs)
                                             post
    SIf b s1 s2       -> wpIf b s1 s2 post
    SWhile b body inv -> wpLoop b body inv post
    SCall f args asgn -> wpCall f args asgn post

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
  let freshen = Name.substituteAll vars freshVars
  (quant, _) <- envGetQSpecs
  bodyWP     <- (case quant of
                   VUniversal   -> weakestPre body inv
                   VExistential -> let
                     nextMeasure = Name.substituteAll vars freshVars measure
                     measureCond = A.Lt measure nextMeasure
                     bodyPost    = A.And [inv, measureCond]
                     in weakestPre body bodyPost)
  let qIdents = namesToIntIdents freshVars
      loopWP  = A.Forall qIdents (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      endWP   = A.Forall qIdents (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
  return $ A.And [inv, loopWP, endWP]

wpCall :: Imp.CallId -> [Imp.AExp] -> [Name] -> Assertion -> Verification Assertion
wpCall cid callArgs assignees post = do
  (quant, specs) <- envGetQSpecs
  case (specAtCallsite specs cid assignees callArgs) of
    Nothing -> error $ "No specification for " ++ show cid ++ "."
               ++ "Specified functions are: " ++ (show $ Spec.funList specs) ++ "."
    Just (cvars, fPre, fPost) ->
      case quant of
        VUniversal   -> return $ A.And [fPre, A.Imp fPost post]
        VExistential -> do
          frAssignees <- envFreshen assignees
          let freshen     = Name.substituteAll assignees frAssignees
              frPost      = freshen post
              frFPost     = freshen fPost
              frIdents    = (namesToIntIdents frAssignees)
              existsPost  = A.Exists frIdents frFPost
              forallPost  = A.Forall frIdents $ A.Imp frFPost frPost
              wp          = A.And [fPre, existsPost, forallPost]
          return $ case cvars of
            [] -> wp
            _  -> A.Exists cvars wp

namesToIntIdents :: Functor f => f Name -> f TypedName
namesToIntIdents = fmap (\v -> TypedName v Name.Int)

namesToIntVars :: Functor f => f Name -> f A.Arith
namesToIntVars = (fmap A.Var) . namesToIntIdents

specAtCallsite :: SpecMap -> Name.Handle -> [Name] -> [Imp.AExp] -> Maybe ([TypedName], Assertion, Assertion)
specAtCallsite specMap funName assignees callArgs = do
  let assigneeVars = map Imp.AVar assignees
  (Spec specParams cvars pre post) <- Map.lookup funName specMap
  let rets       = Spec.retVars $ length assignees
  let fromIdents = map (\n -> TypedName n Name.Int) (rets ++ specParams)
  let toAriths   = map Imp.aexpToArith (assigneeVars ++ callArgs)
  let bind a     = foldr (uncurry A.subArith) a (zip fromIdents toAriths)
  return (cvars, bind pre, bind post)
