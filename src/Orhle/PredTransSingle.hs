module Orhle.PredTransSingle
  ( Loop(..)
  , strongestPost
  , strongestPostQ
  , weakestPre
  , weakestPreQ
  ) where

import           Ceili.Assertion ( Assertion(..) )
import qualified Ceili.Assertion as A
import           Ceili.Language.FunImp
import           Ceili.Name  ( Name, TypedName(..) )
import qualified Ceili.Name as Name
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Orhle.PredTransTypes ( Loop(..) )
import           Orhle.Spec ( Spec(..) )
import qualified Orhle.Spec as Spec
import           Orhle.Triple ( RevProgram )
import           Orhle.VerifierEnv

------------------------------------
-- Weakest Precondition Semantics --
------------------------------------

weakestPreQ :: VQuant -> RevProgram -> Assertion -> Verification Assertion
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
                                             (aexpToArith rhs)
                                             post
    SIf b s1 s2       -> wpIf b s1 s2 post
    SWhile b body inv -> wpLoop b body inv post
    SCall f args asgn -> wpCall f args asgn post

wpIf :: BExp -> RevProgram -> RevProgram -> Assertion -> Verification Assertion
wpIf condB tBranch eBranch post = do
  wpT <- weakestPre tBranch post
  wpE <- weakestPre eBranch post
  let cond   = bexpToAssertion condB
      ncond  = A.Not $ cond
  return $ A.And [A.Imp cond wpT, A.Imp ncond wpE]

wpCall :: CallId -> [AExp] -> [Name] -> Assertion -> Verification Assertion
wpCall cid callArgs assignees post = do
  (cvars, fPre, fPost) <- specAtCallsite cid callArgs
  let retVars  = Spec.retVars $ length assignees
  frAssignees <- envFreshenAll assignees
  let frPost   = Name.substituteAll assignees frAssignees post
  let frFPost  = Name.substituteAll retVars   frAssignees fPost
  (quant, _)  <- envGetQSpecs
  case quant of
    VUniversal   -> return $ A.And [fPre, A.Imp frFPost frPost]
    VExistential -> let
      frNames     = (Name.toIntNames frAssignees)
      existsPost  = A.Exists frNames frFPost
      forallPost  = A.Forall frNames $ A.Imp frFPost frPost
      in return $ case (length cvars) of
                    0 -> A.And [fPre, existsPost, forallPost]
                    _ -> A.Exists cvars $ A.And [fPre, existsPost, forallPost]

wpLoop :: BExp -> RevProgram -> (Assertion, A.Arith) -> Assertion -> Verification Assertion
wpLoop condB body (inv, measure) post = do
  let cond    = bexpToAssertion condB
      varSet  = Set.unions [Name.namesIn condB, Name.namesIn body]
      vars    = Set.toList varSet
  freshVars  <- envFreshenAll vars
  let freshen = Name.substituteAll vars freshVars
  (quant, _) <- envGetQSpecs
  bodyWP     <- (case quant of
                   VUniversal   -> weakestPre body inv
                   VExistential -> let
                     nextMeasure = Name.substituteAll vars freshVars measure
                     measureCond = A.Lt measure nextMeasure
                     bodyPost    = A.And [inv, measureCond]
                     in weakestPre body bodyPost)
  let qNames = Name.toIntNames freshVars
      loopWP = A.Forall qNames (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      endWP  = A.Forall qNames (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
  return $ A.And [inv, loopWP, endWP]


---------------------------------------
-- Strongest Postcondition Semantics --
---------------------------------------

strongestPostQ :: VQuant -> Program -> Assertion -> Verification Assertion
strongestPostQ quant prog pre = do
  origQuant <- envGetQuant
  envSetQuant quant
  result <- strongestPost prog pre
  envSetQuant origQuant
  return result

strongestPost :: Program -> Assertion -> Verification Assertion
strongestPost prog pre = do
  (quant, specs) <- envGetQSpecs
  case prog of
    SSkip         -> return pre
    SSeq []       -> return pre
    SSeq (s:ss)   -> strongestPost s pre >>= strongestPost (SSeq ss)
    SAsgn lhs rhs -> spAsgn lhs rhs pre
    SIf b s1 s2   -> do
      let cond = bexpToAssertion b
      postS1  <- strongestPost s1 $ A.And [pre, cond]
      postS2  <- strongestPost s2 $ A.And [pre, A.Not cond]
      return $ A.Or [postS1, postS2]
    loop@(SWhile b body (inv, measure)) -> do
      let cond = bexpToAssertion b
      -- TODO: add invariant vc
      return $ A.And [A.Not cond, inv]
    SCall cid args assignees -> spCall cid args assignees pre

spAsgn :: Name -> AExp -> Assertion -> Verification Assertion
spAsgn lhs rhs pre = do
  freshLhs    <- envFreshen lhs
  let subPre   = Name.substituteAll [lhs] [freshLhs] pre
  let rhsArith = aexpToArith rhs
  let subRhs   = A.subArith (Name.toIntName lhs) (A.toIntVar freshLhs) rhsArith
  return $ A.Exists [Name.toIntName freshLhs] $ A.And [A.Eq (A.toIntVar lhs) subRhs, subPre]

spCall :: CallId -> [AExp] -> [Name] -> Assertion -> Verification Assertion
spCall cid args assignees pre = do
  (cvars, fPre, fPost) <- specAtCallsite cid args
  let retVars       = Spec.retVars $ length assignees
  freshAssignees   <- envFreshenAll assignees
  let freshenedPre  = Name.substituteAll assignees freshAssignees pre
  let freshenedFPre = Name.substituteAll assignees freshAssignees fPre
  let subbedFPost   = Name.substituteAll retVars   assignees      fPost
  (quant, _)       <- envGetQSpecs
  case quant of
    VUniversal -> do
      -- TODO: add pre -> fPre vc
      return $ A.Exists (Name.toIntNames freshAssignees) $ A.And [ freshenedPre, subbedFPost ]
    VExistential -> do
--      return $ A.Exists (Name.toIntNames freshAssignees) $ A.And [ freshenedPre, subbedFPost ]
--      envAddChoiceVars cvars
--      envAddChoiceVars (Name.toIntNames assignees)
      return $ A.Exists (Name.toIntNames freshAssignees) $
               A.Exists (cvars) $
               A.And [ freshenedPre
                     , freshenedFPre
                     , subbedFPost ]

---------------
-- Utilities --
---------------

specAtCallsite :: CallId -> [AExp] -> Verification ([TypedName], Assertion, Assertion)
specAtCallsite cid callArgs = do
  (quant, specMap) <- envGetQSpecs
  case Map.lookup cid specMap of
    Nothing -> throwError $ "No " ++ (show quant) ++ " specification for " ++ show cid ++ ". "
               ++ "Specified " ++ (show quant) ++ " functions are: " ++ (show $ Map.keys specMap) ++ "."
    Just (Spec specParams cvars pre post) -> let
      fromNames   = map (\n -> TypedName n Name.Int) specParams
      toAriths    = map aexpToArith callArgs
      bind a      = foldr (uncurry A.subArith) a (zip fromNames toAriths)
      cvarNames   = map tnName cvars
      in do
        frCvarNames <- envFreshenAll cvarNames
        let frCvars = map (Name.substituteAll cvarNames frCvarNames) cvars
        let freshenCvars = Name.substituteAll cvarNames frCvarNames
        return (frCvars, freshenCvars $ bind pre, freshenCvars $ bind post)
