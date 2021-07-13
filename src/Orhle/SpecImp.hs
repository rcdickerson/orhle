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
  , ImpAsgn(..)
  , ImpBackwardPT(..)
  , ImpCall(..)
  , ImpExpr(..)
  , ImpForwardPT(..)
  , ImpIf(..)
  , ImpSkip(..)
  , ImpSeq(..)
  , ImpSpecCall(..)
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , Name(..)
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
  , impSpecCall
  , returnVars
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
data SpecImpEnv   = SpecImpEnv { sie_impls  :: FunImplEnv
                               , sie_aspecs :: SpecMap
                               , sie_especs :: SpecMap }

instance CollectableNames SpecImpEnv where
  namesIn (SpecImpEnv impls aspecs especs) =
    Set.unions [ Set.unions $ map namesIn (Map.elems impls)
               , Set.unions $ map namesIn (Map.elems aspecs)
               , Set.unions $ map namesIn (Map.elems especs) ]

sie_specs :: SpecImpEnv -> SpecImpQuant -> SpecMap
sie_specs env quant = case quant of
  SIQ_Universal   -> sie_aspecs env
  SIQ_Existential -> sie_especs env

returnVars :: Int -> [Name]
returnVars 0   = []
returnVars 1   = [Name "ret!" 0]
returnVars len = map (\i -> Name "ret" i) [0..(len - 1)]


------------------------------
-- Specified Function Calls --
------------------------------

data ImpSpecCall e = ImpSpecCall CallId [AExp] [Name]
  deriving (Eq, Ord, Show, Functor)

instance CollectableNames (ImpSpecCall e) where
  namesIn (ImpSpecCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance FreshableNames (ImpSpecCall e) where
  freshen (ImpSpecCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ ImpSpecCall cid args' assignees'

instance MappableNames (ImpSpecCall e) where
  mapNames f (ImpSpecCall cid args assignees) =
    ImpSpecCall cid (map (mapNames f) args) (map f assignees)


---------------------
-- SpecImp Language --
---------------------

type SpecImpProgram = ImpExpr ( ImpSpecCall
                            :+: ImpCall
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

impSpecCall :: (ImpSpecCall :<: f) => CallId -> [AExp] -> [Name] -> ImpExpr f
impSpecCall cid args assignees = inject $ ImpSpecCall cid args assignees


----------------------------------
-- Backward Predicate Transform --
----------------------------------

instance FunImplLookup (SpecImpQuant, SpecImpEnv) where
  lookupFunImpl (_, env) name = lookupFunImpl (sie_impls env) name

instance ImpBackwardPT (SpecImpQuant, SpecImpEnv) SpecImpProgram where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post

instance ImpBackwardPT (SpecImpQuant, SpecImpEnv) (ImpSpecCall e) where
  impBackwardPT (quant, env) call@(ImpSpecCall cid args assignees) post =
    case (Map.lookup cid $ sie_impls env, Map.lookup cid $ sie_specs env quant) of
      (Nothing, Nothing) ->
        throwError $ "No implementation or specification for " ++ cid
      (Just _, _) ->
        impBackwardPT (quant, env) (ImpCall cid args assignees) post
      (_, Just spec) ->
        case quant of
          SIQ_Universal   -> universalSpecPT spec call post
          SIQ_Existential -> existentialSpecPT spec call post

universalSpecPT :: Specification -> (ImpSpecCall e) -> Assertion -> Ceili Assertion
universalSpecPT spec (ImpSpecCall _ args assignees) post = do
  (_, fPre, fPost) <- specAtCallsite spec args
  let retVars  = returnVars $ length assignees
  frAssignees <- envFreshen assignees
  let frPost   = substituteAll assignees frAssignees post
  let frFPost  = substituteAll retVars   frAssignees fPost
  return $ And [fPre, Imp frFPost frPost]

existentialSpecPT :: Specification -> (ImpSpecCall e) -> Assertion -> Ceili Assertion
existentialSpecPT spec (ImpSpecCall _ args assignees) post = do
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
