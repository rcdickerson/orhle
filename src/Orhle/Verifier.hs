module Orhle.Verifier
  ( Failure(..)
  , Success(..)
  , Verifier
  , rhleVerifier
  ) where

import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion )
import qualified Orhle.Assertion as A
import           Orhle.Imp.ImpLanguage
import qualified Orhle.MapNames as Names
import           Orhle.Spec
import qualified Orhle.SMT as SMT
import           Orhle.Triple

type Verifier = AESpecs -> RhleTriple -> IO (Either Failure Success)
data Failure  = Failure { failureVcs :: Assertion,  model :: String }
data Success  = Success { successVcs :: Assertion }

data VCQuant = VCUniversal
             | VCExistential
             deriving Show

rhleVerifier :: Verifier
rhleVerifier specs (RhleTriple pre aProgs eProgs post) = let
  vcsA = vcsForProgs VCExistential (especs specs) eProgs post
  vcsE = vcsForProgs VCUniversal   (aspecs specs) aProgs vcsA
  vcs  = A.Imp pre vcsE
  in do
    result <- SMT.checkValid vcs
    case result of
      SMT.Sat m -> return . Left  $ Failure vcs m
      SMT.Unsat -> return . Right $ Success vcs

vcsForProgs :: VCQuant -> SpecMap -> [Stmt] -> Assertion -> Assertion
vcsForProgs quant specs progs post = foldr (generateVCs quant specs) post progs

generateVCs :: VCQuant -> SpecMap -> Stmt -> Assertion -> Assertion
generateVCs quant specs stmt post =
  let vcs = generateVCs quant specs in
  case stmt of
    SSkip          -> post
    SSeq []        -> post
    SSeq (s:ss)    -> vcs s $ vcs (SSeq ss) post
    SAsgn lhs rhs  -> A.subArith (A.Ident lhs A.Int) (aexpToArith rhs) post
    SIf b s1 s2 -> let
      cond   = bexpToAssertion b
      ncond  = A.Not $ cond
      vcs1   = vcs s1 post
      vcs2   = vcs s2 post
      vcIf   = A.Imp cond  vcs1
      vcElse = A.Imp ncond vcs2
      in A.And [vcIf, vcElse]
    loop@(SWhile b body (inv, measure, _)) -> let
      cond        = bexpToAssertion b
      loopVars    = Set.toList $ svars loop
      freshVars   = locallyFreshVars loopVars
      bodyVC      = (case quant of
                       VCUniversal -> vcs body inv
                       VCExistential -> let
                         nextMeasure = Names.substituteAll loopVars freshVars measure
                         measureCond = A.Lt measure nextMeasure
                         bodyPost    = A.And [inv, measureCond]
                         in vcs body bodyPost)
      freshIdents = varsToIntIdents freshVars
      freshen     = Names.substituteAll loopVars freshVars
      loopVC      = A.Forall freshIdents (freshen $ A.Imp (A.And [cond, inv]) bodyVC)
      endVC       = A.Forall freshIdents (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
      in A.And [inv, loopVC, endVC]
    SCall assignees cparams funName ->
      case (specAtCallsite assignees cparams funName specs) of
        Nothing -> error $ "No " ++ (show quant) ++ " specification for " ++ funName ++
                   ". Specified functions are: " ++ (show $ funList specs)
        Just (cvars, fPre, fPost) ->
          case quant of
            VCUniversal   -> A.And [fPre, A.Imp fPost post]
            VCExistential -> let
              frAssignees = locallyFreshVars assignees
              freshen     = Names.substituteAll assignees frAssignees
              frPost      = freshen post
              frFPost     = freshen fPost
              frIdents    = (varsToIntIdents frAssignees)
              existsPost  = A.Exists frIdents frFPost
              forallPost  = A.Forall frIdents $ A.Imp frFPost frPost
              vcAssertion = A.And [fPre, existsPost, forallPost]
              in case cvars of
                  [] -> vcAssertion
                  _  -> A.Exists cvars vcAssertion

varsToIntIdents :: [Var] -> [A.Ident]
varsToIntIdents = map (\v -> A.Ident v A.Int)

-- Returns a freshened version of the input Var array, where "fresh" is with
-- respect to the input array only: the variables in the output array will not
-- exist in the input array. This kind of limited freshening is adequate for
-- RHLE verification tasks and is simpler than tracking variable indices across
-- larger scopes.
locallyFreshVars :: [Var] -> [Var]
locallyFreshVars invars = map (freshen 0) invars
  where
    freshen x v =
      let proposed = v ++ "!" ++ (show x) in
      if proposed `elem` invars then freshen (x + 1) v else proposed
