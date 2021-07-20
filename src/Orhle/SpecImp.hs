{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}

module Orhle.SpecImp
  ( AExp(..)
  , BExp(..)
  , CallId
  , EvalImp(..)
  , Fuel(..)
  , FuelTank(..)
  , FunEvalContext(..)
  , FunImpl(..)
  , FunImplEnv
  , FunImplLookup(..)
  , FunImpProgram
  , FunSpecEnv(..)
  , GetLoop(..)
  , ImpAsgn(..)
  , ImpBackwardPT(..)
  , ImpCall(..)
  , ImpExpr(..)
  , ImpForwardPT(..)
  , ImpIf(..)
  , ImpSkip(..)
  , ImpSeq(..)
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , Name(..)
  , SpecCall(..)
  , SpecImpEnv(..)
  , SpecImpProgram
  , SpecImpQuant(..)
  , Specification(..)
  , SpecMap
  , State
  , impAsgn
  , impCall
  , impIf
  , impSeq
  , impSkip
  , impWhile
  , impWhileWithMeta
  , returnVars
  , specCall
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.AExp
import Ceili.Language.Compose
import Ceili.Language.FunImp
import Ceili.Name
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set


--------------------
-- Specifications --
--------------------

data Specification = Specification
  { spec_params        :: [Name]
  , spec_choiceVars    :: [TypedName]
  , spec_preCondition  :: Assertion
  , spec_postCondition :: Assertion
  } deriving Show

instance CollectableNames Specification where
  namesIn (Specification ps cs pre post) = Set.unions allNames
    where
      allNames = [ Set.fromList ps
                 , Set.unions $ map namesIn cs
                 , namesIn pre
                 , namesIn post ]

instance MappableNames Specification where
  mapNames f (Specification ps cs pre post) =
    Specification (mapNames f ps)
                  (mapNames f cs)
                  (mapNames f pre)
                  (mapNames f post)


-------------------------------
-- Specification Environment --
-------------------------------

type SpecMap      = Map Handle Specification
data SpecImpQuant = SIQ_Universal | SIQ_Existential
data FunSpecEnv   = FunSpecEnv { fse_aspecs :: SpecMap
                               , fse_especs :: SpecMap }

instance CollectableNames FunSpecEnv where
  namesIn (FunSpecEnv aspecs especs) =
    Set.unions [ Set.unions $ map namesIn (Map.elems aspecs)
               , Set.unions $ map namesIn (Map.elems especs) ]

fse_qspecs :: FunSpecEnv -> SpecImpQuant -> SpecMap
fse_qspecs env quant = case quant of
  SIQ_Universal   -> fse_aspecs env
  SIQ_Existential -> fse_especs env

returnVars :: Int -> [Name]
returnVars 0   = []
returnVars 1   = [Name "ret!" 0]
returnVars len = map (\i -> Name "ret" i) [0..(len - 1)]


------------------------------
-- Specified Function Calls --
------------------------------

data SpecCall e = SpecCall { sc_callId    :: CallId
                           , sc_args      :: [AExp]
                           , sc_assignees :: [Name]
                           }
  deriving (Eq, Ord, Show, Functor)

instance CollectableNames (SpecCall e) where
  namesIn (SpecCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance FreshableNames (SpecCall e) where
  freshen (SpecCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ SpecCall cid args' assignees'

instance MappableNames (SpecCall e) where
  mapNames f (SpecCall cid args assignees) =
    SpecCall cid (map (mapNames f) args) (map f assignees)


---------------------
-- SpecImp Language --
---------------------

type SpecImpProgram = ImpExpr ( SpecCall
                            :+: ImpSkip
                            :+: ImpAsgn
                            :+: ImpSeq
                            :+: ImpIf
                            :+: ImpWhile )

instance CollectableNames SpecImpProgram where
  namesIn (In f) = namesIn f

instance MappableNames SpecImpProgram where
  mapNames func (In f) = In $ mapNames func f

instance FreshableNames SpecImpProgram where
  freshen (In f) = return . In =<< freshen f

specCall :: (SpecCall :<: f) => CallId -> [AExp] -> [Name] -> ImpExpr f
specCall cid args assignees = inject $ SpecCall cid args assignees

toImpCall :: SpecCall e -> ImpCall e
toImpCall (SpecCall cid args assignees) = ImpCall cid args assignees


---------------
-- Utilities --
---------------

class GetLoop e where
  getLoop :: e -> Maybe (ImpWhile SpecImpProgram)
instance (GetLoop (f e), GetLoop (g e)) => GetLoop ((f :+: g) e) where
  getLoop (Inl f) = getLoop f
  getLoop (Inr g) = getLoop g
instance GetLoop SpecImpProgram where
  getLoop (In p) = getLoop p
instance GetLoop (ImpSkip e)  where getLoop _ = Nothing
instance GetLoop (ImpAsgn e)  where getLoop _ = Nothing
instance GetLoop (ImpSeq e)   where getLoop _ = Nothing
instance GetLoop (ImpIf e)    where getLoop _ = Nothing
instance GetLoop (ImpCall e)  where getLoop _ = Nothing
instance GetLoop (SpecCall e) where getLoop _ = Nothing
instance GetLoop (ImpWhile SpecImpProgram) where getLoop = Just

----------------------------------
-- Backward Predicate Transform --
----------------------------------

data SpecImpEnv e = SpecImpEnv { sie_impls :: FunImplEnv e
                               , sie_specs :: FunSpecEnv
                               }

sie_qspecs :: SpecImpEnv e -> SpecImpQuant -> SpecMap
sie_qspecs = fse_qspecs . sie_specs

instance FunImplLookup (SpecImpQuant, SpecImpEnv e) e where
  lookupFunImpl (_, env) = lookupFunImpl (sie_impls env)

instance ImpBackwardPT (SpecImpQuant, SpecImpEnv SpecImpProgram) SpecImpProgram where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post

instance (ImpBackwardPT (SpecImpQuant, SpecImpEnv e) e, FreshableNames e) =>
         ImpBackwardPT (SpecImpQuant, SpecImpEnv e) (SpecCall e) where
  impBackwardPT (quant, env) call post =
    let cid = sc_callId call
    in case (Map.lookup cid $ sie_impls env,
             Map.lookup cid $ sie_qspecs env quant) of
      (Nothing, Nothing) ->
        throwError $ "No implementation or specification for " ++ cid
      (Just _, _) ->
        impBackwardPT (quant, env) (toImpCall call) post
      (_, Just spec) ->
        case quant of
          SIQ_Universal   -> universalSpecPT spec call post
          SIQ_Existential -> existentialSpecPT spec call post

universalSpecPT :: Specification -> (SpecCall e) -> Assertion -> Ceili Assertion
universalSpecPT spec (SpecCall _ args assignees) post = do
  (_, fPre, fPost) <- specAtCallsite spec args
  let retVars  = returnVars $ length assignees
  frAssignees <- envFreshen assignees
  let frPost   = substituteAll assignees frAssignees post
  let frFPost  = substituteAll retVars   frAssignees fPost
  return $ And [fPre, Imp frFPost frPost]

existentialSpecPT :: Specification -> (SpecCall e) -> Assertion -> Ceili Assertion
existentialSpecPT spec (SpecCall _ args assignees) post = do
  (cvars, fPre, fPost) <- specAtCallsite spec args
  let retVars  = returnVars $ length assignees
  frAssignees <- envFreshen assignees
  let frPost     = substituteAll assignees frAssignees post
      frFPost    = substituteAll retVars   frAssignees fPost
      frNames    = map (\n -> TypedName n Int) frAssignees
      existsPost = Exists frNames frFPost
      forallPost = Forall frNames $ Imp frFPost frPost
  return $ case (length cvars) of
    0 -> And [fPre, existsPost, forallPost]
    _ -> Exists cvars $ And [fPre, existsPost, forallPost]

specAtCallsite :: Specification -> [AExp] -> Ceili ([TypedName], Assertion, Assertion)
specAtCallsite (Specification specParams cvars pre post) callArgs = let
  fromNames   = map (\n -> TypedName n Int) specParams
  toAriths    = map aexpToArith callArgs
  bind a      = foldr (uncurry subArith) a (zip fromNames toAriths)
  cvarNames   = map tnName cvars
  in do
    frCvarNames <- envFreshen cvarNames
    let frCvars = map (substituteAll cvarNames frCvarNames) cvars
    let freshenCvars = substituteAll cvarNames frCvarNames
    return (frCvars, freshenCvars $ bind pre, freshenCvars $ bind post)
