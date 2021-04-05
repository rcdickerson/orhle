module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , Verifier
  , rhleVerifier
  ) where

import           Control.Monad.Except ( ExceptT, runExceptT, throwError )
import           Control.Monad.IO.Class ( liftIO )
import           Control.Monad.Trans.State
import           Data.Either ( partitionEithers )
import           Data.List ( partition )
import qualified Data.Map as Map
import           Data.Maybe ( catMaybes )
import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion )
import qualified Orhle.Assertion as A
import qualified Orhle.InvariantInference as Inf
import           Orhle.Imp.ImpLanguage ( FunImplEnv, Program(..), BExp )
import qualified Orhle.Imp.ImpLanguage as Imp
import           Orhle.Inliner ( inline )
import           Orhle.Name  ( Name(..), NextFreshIds, TypedName(..), namesIn )
import qualified Orhle.Name as Name
import           Orhle.ShowSMT ( showSMT )
import qualified Orhle.SMT as SMT
import           Orhle.Spec ( AESpecs(..), Spec(..), SpecMap )
import qualified Orhle.Spec as Spec
import           Orhle.Triple

import Debug.Trace

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

type Verification a = StateT Env (ExceptT String IO) a

envFreshen :: Traversable t => t Name -> Verification (t Name)
envFreshen names = do
  Env quant specs freshMap <- get
  let (freshX, freshMap') = Name.freshen names freshMap
  put $ Env quant specs freshMap'
  return freshX

envSetQuant :: VQuant -> Verification ()
envSetQuant quant = do
  Env _ specs freshMap <- get
  put $ Env quant specs freshMap

envGetQuant :: Verification VQuant
envGetQuant = do
  Env quant _ _ <- get
  return quant

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
data Failure  = Failure { failMessage :: String } deriving Show
data Success  = Success { }

rhleVerifier :: Verifier
rhleVerifier specs impls (RhleTriple pre aProgs eProgs post) =
  case doInline impls aProgs eProgs of
    Left errs -> return . Left $ Failure $ "Problems inlining: " ++ show errs
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
          Left  msg -> Left  $ Failure msg
          Right _   -> Right $ Success

doInline :: FunImplEnv -> [Program] -> [Program] -> Either [String] ([Program], [Program])
doInline impls aProgs eProgs = let
  inmap = partitionEithers . map (inline impls)
  (errorAs, inAs) = inmap aProgs
  (errorEs, inEs) = inmap eProgs
  in case (errorAs ++ errorEs) of
    []   -> Right (inAs, inEs)
    errs -> Left $ errs

runVCs :: AESpecs -> RhleTriple -> IO (Either String Assertion)
runVCs specs triple = runExceptT $ evalStateT (stepUntilDone $ revTriple triple) (buildEnv specs triple)

stepUntilDone :: RevRhleTriple -> Verification Assertion
stepUntilDone triple = case filterEmptyProgs triple of
  RevRhleTriple pre [] [] post -> return $ A.Imp pre post
  _                            -> step triple >>= stepUntilDone

step :: RevRhleTriple -> Verification RevRhleTriple
step triple = do
  nonLoop <- stepFirstNonLoop triple
  case nonLoop of
    Nothing -> fuseLoops triple -- stepTemp triple
    Just triple' -> return triple'

stepTemp :: RevRhleTriple -> Verification RevRhleTriple
stepTemp t =
  let triple@(RevRhleTriple pre aprogs eprogs post) = filterEmptyProgs t
  in case (aprogs, eprogs) of
    ([], []) -> return triple
    (_, (eprog:rest)) -> do
      post' <- weakestPreQ VExistential eprog post
      return $ RevRhleTriple pre aprogs rest post'
    (aprog:rest, _) -> do
      post' <- weakestPreQ VUniversal aprog post
      return $ RevRhleTriple pre rest eprogs post'

stepFirstNonLoop :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
stepFirstNonLoop triple = let
  RevRhleTriple pre aprogs eprogs post = filterEmptyProgs triple
  (aloops, as) = partition isLoop aprogs
  (eloops, es) = partition isLoop eprogs
  in case (as, es) of
    ([], []) -> return Nothing
    (_, eprog:rest) -> do
      let (hd, eprog') = headProg eprog
      post' <- weakestPreQ VExistential hd post
      return $ Just $ RevRhleTriple pre aprogs (eprog':(rest ++ eloops)) post'
    (aprog:rest, _) -> do
      let (hd, aprog') = headProg aprog
      post' <- weakestPreQ VUniversal aprog post
      return $ Just $ RevRhleTriple pre (aprog':(rest ++ aloops)) eprogs post'

fuseLoops :: RevRhleTriple -> Verification RevRhleTriple
fuseLoops triple = let
  (aloops, eloops, iv, RevRhleTriple pre aprogs eprogs post) = extractLoops triple
  in do
    post' <- wpLoopFusion aloops eloops iv post
    return $ RevRhleTriple pre aprogs eprogs post'

extractLoops :: RevRhleTriple -> ( [(BExp, Program)], [(BExp, Program)], (Assertion, A.Arith), RevRhleTriple )
extractLoops (RevRhleTriple pre aprogs eprogs post) = let
  aloops = catMaybes $ map headLoop aprogs
  eloops = catMaybes $ map headLoop eprogs
  condBodyOf (cond, body, _, _) = (cond, body)
  invarVarOf (_, _, iv, _)      = iv
  restOf     (_, _, _, rest)    = rest
  iv = invarVarOf $ head (aloops ++ eloops) -- TODO: Match invariants
  triple' = filterEmptyProgs $ RevRhleTriple pre (map restOf aloops) (map restOf eloops) post
  in (map condBodyOf aloops, map condBodyOf eloops, iv, triple')

headProg :: Program -> (Program, Program)
headProg prog = case prog of
  SSkip        -> (prog, SSkip)
  SAsgn _ _    -> (prog, SSkip)
  SSeq []      -> (SSkip, SSkip)
  SSeq (s:ss)  -> let (s', ss') = headProg s in (s', SSeq $ ss':ss)
  SIf _ _ _    -> (prog, SSkip)
  SWhile _ _ _ -> (prog, SSkip)
  SCall _ _ _  -> (prog, SSkip)

isLoop :: Program -> Bool
isLoop prog = case headLoop prog of
  Nothing -> False
  Just _  -> True

headLoop :: Program -> Maybe (BExp, Program, (Assertion, A.Arith), Program)
headLoop prog = case filterEmpty prog of
  Nothing                    -> Nothing
  Just (SWhile cond body iv) -> Just (cond, body, iv, SSkip)
  Just (SSeq (hd:_))         -> headLoop hd
  _                          -> Nothing

filterEmpty :: Program -> Maybe Program
filterEmpty prog = case prog of
  SSkip            -> Nothing
  SAsgn _ _        -> Just prog
  SSeq []          -> Nothing
  SSeq ss          -> case catMaybes $ map filterEmpty ss of
                        []  -> Nothing
                        ss' -> Just $ SSeq ss'
  SIf _ _ _        -> Just prog
  SWhile c body iv -> (filterEmpty body) >>= \body' -> return $ SWhile c body' iv
  SCall _ _ _      -> Just prog

filterEmptyProgs :: RevRhleTriple -> RevRhleTriple
filterEmptyProgs (RevRhleTriple pre aprogs eprogs post) =
  let filtered = catMaybes . (map filterEmpty)
  in RevRhleTriple pre (filtered aprogs) (filtered eprogs) post

------------------------------------
-- Weakest Precondition Semantics --
------------------------------------

weakestPreQ :: VQuant -> Program -> Assertion -> Verification Assertion
weakestPreQ quant prog post = do
  origQuant <- envGetQuant
  envSetQuant quant
  result <- weakestPre prog post
  envSetQuant origQuant
  return result

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
  let qNames = namesToIntNames freshVars
      loopWP = A.Forall qNames (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      endWP  = A.Forall qNames (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
  return $ A.And [inv, loopWP, endWP]

wpLoopFusion :: [(BExp, Program)] ->
                [(BExp, Program)] ->
                (Assertion, A.Arith) ->
                Assertion ->
                Verification Assertion
wpLoopFusion aloops eloops (invar, var) post = do
  let abodies   = map snd aloops
      ebodies   = map snd eloops
      aconds    = map (Imp.bexpToAssertion . fst) aloops
      econds    = map (Imp.bexpToAssertion . fst) eloops
      anconds   = map A.Not aconds
      enconds   = map A.Not econds
      allBodies = abodies ++ ebodies
      allConds  = aconds ++ econds
      allNConds = anconds ++ enconds
      varSet    = Set.unions $ map namesIn allConds ++ map namesIn allBodies
      vars      = Set.toList varSet
      bodyTrip  = RevRhleTriple (A.And $ invar:allConds) abodies ebodies invar
  traceM $ "\n ***** bodyTrip (rev): " ++ ppRevRhleTriple bodyTrip
  freshVars    <- envFreshen vars
  let freshen   = Name.substituteAll vars freshVars
  let qNames    = namesToIntNames freshVars
  let impPost   = freshen $ A.Imp (A.And $ invar:allNConds) post
  inductive    <- (stepUntilDone bodyTrip) >>= (return . freshen)

  unfreshInductive    <- (stepUntilDone bodyTrip)
  traceM $ "\n ***** unfresh inductive VC: " ++ showSMT unfreshInductive
  traceM $ "\n ***** inductive VC: " ++ showSMT inductive

  let sameIters = freshen $ A.Imp (A.And [invar, (A.Not $ A.And allConds)]) (A.And allNConds)
  -- TODO: Variant
  return $ A.And [ invar, A.Forall qNames impPost, A.Forall qNames inductive, A.Forall qNames sameIters]

checkValid :: Assertion -> Verification ()
checkValid assertion = do
  result <- liftIO $ SMT.checkValid assertion
  case result of
    SMT.Valid        -> return ()
    SMT.Invalid msg  -> throwError msg
    SMT.ValidUnknown -> throwError $ "Solver returned unknown validating " ++ show assertion

wpCall :: Imp.CallId -> [Imp.AExp] -> [Name] -> Assertion -> Verification Assertion
wpCall cid callArgs assignees post = do
  (cvars, fPre, fPost) <- specAtCallsite cid callArgs
  let retVars     = Spec.retVars $ length assignees
  frAssignees    <- envFreshen assignees
  let frPost      = Name.substituteAll assignees frAssignees post
  let frFPost     = Name.substituteAll retVars   frAssignees fPost
  (quant, _)     <- envGetQSpecs
  case quant of
    VUniversal   -> do
      return $ A.And [fPre, A.Imp frFPost frPost]
    VExistential -> let
      frNames     = (namesToIntNames frAssignees)
      existsPost  = A.Exists frNames frFPost
      forallPost  = A.Forall frNames $ A.Imp frFPost frPost
      wp          = A.And [fPre, existsPost, forallPost]
      in return $ case cvars of
        [] -> wp
        _  -> A.Exists cvars wp

namesToIntNames :: Functor f => f Name -> f TypedName
namesToIntNames = fmap (\v -> TypedName v Name.Int)

namesToIntVars :: Functor f => f Name -> f A.Arith
namesToIntVars = (fmap A.Var) . namesToIntNames

specAtCallsite :: Imp.CallId -> [Imp.AExp] -> Verification ([TypedName], Assertion, Assertion)
specAtCallsite cid callArgs = do
  (quant, specMap) <- envGetQSpecs
  case Map.lookup cid specMap of
    Nothing -> throwError $ "No " ++ (show quant) ++ " specification for " ++ show cid ++ ". "
               ++ "Specified " ++ (show quant) ++ " functions are: " ++ (show $ Map.keys specMap) ++ "."
    Just (Spec specParams cvars pre post) -> let
      fromNames = map (\n -> TypedName n Name.Int) specParams
      toAriths  = map Imp.aexpToArith callArgs
      bind a    = foldr (uncurry A.subArith) a (zip fromNames toAriths)
      in return (cvars, bind pre, bind post)
