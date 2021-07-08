{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}

module Orhle.SpecImp
  ( FunSpecEnv
  , SpecImpEnv(..)
  , SpecImpProgram
  , SpecImpQuant
  , Specification(..)
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

type FunSpecEnv   = Map Handle Specification
data SpecImpQuant = SIQ_Universal | SIQ_Existential
data SpecImpEnv   = SpecImpEnv { sie_impls :: FunImplEnv
                               , sie_specs :: FunSpecEnv
                               , sie_quant :: SpecImpQuant }

instance FunImplLookup SpecImpEnv where
  lookupFunImpl env name = lookupFunImpl (sie_impls env) name

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

instance ImpBackwardPT SpecImpEnv SpecImpProgram where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post

instance ImpBackwardPT SpecImpEnv (ImpSpecCall e) where
  impBackwardPT env call@(ImpSpecCall cid args assignees) post =
    case (Map.lookup cid $ sie_impls env, Map.lookup cid $ sie_specs env) of
      (Nothing, Nothing) ->
        throwError $ "No implementation or specification for " ++ cid
      (Just _, _) ->
        impBackwardPT env (ImpCall cid args assignees) post
      (_, Just spec) ->
        case sie_quant env of
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
