{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}

module Orhle.SpecImp
  ( FunImpProgram
  , Specification(..)
  , prefixSpecifications
  , returnVars
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Language.FunImp
import Ceili.Name
import Data.List ( isPrefixOf )
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

type FunSpecEnv = Map Handle Specification

returnVars :: Int -> [Name]
returnVars 0   = []
returnVars 1   = [Name "ret!" 0]
returnVars len = map (\i -> Name "ret" i) [0..(len - 1)]


---------------------------------------------
-- Backward Predicate Transform: Universal --
---------------------------------------------

class ImpBackwardPTA c p where
  impBackwardPTA :: c -> p -> Assertion -> Ceili Assertion

instance ImpBackwardPTA (FunImplEnv, FunSpecEnv) (ImpSkip e) where
  impBackwardPTA (impls, _) skip post = impBackwardPT impls skip post

instance ImpBackwardPTA (FunImplEnv, FunSpecEnv) (ImpAsgn e) where
  impBackwardPTA (impls, _) asgn post = impBackwardPT impls asgn post

instance ImpBackwardPTA (FunImplEnv, FunSpecEnv) e =>
  ImpBackwardPTA (FunImplEnv, FunSpecEnv) (ImpSeq e) where
    impBackwardPTA ctx (ImpSeq stmts) post = case stmts of
      []     -> return post
      (s:ss) -> do
        post' <- impBackwardPTA ctx (ImpSeq ss) post
        impBackwardPTA ctx s post'

instance (ImpBackwardPTA FunImplEnv e) =>
  ImpBackwardPTA (FunImplEnv, FunSpecEnv) (ImpIf e) where
    impBackwardPTA ctx (ImpIf c t e) post = do
      wpT <- impBackwardPTA ctx t post
      wpE <- impBackwardPTA ctx e post
      let cond   = bexpToAssertion c
          ncond  = Not $ cond
      return $ And [Imp cond wpT, Imp ncond wpE]

instance (CollectableNames e, ImpBackwardPT FunImplEnv e, ImpForwardPT FunImplEnv e) =>
  ImpBackwardPTA (FunImplEnv, FunSpecEnv) (ImpWhile e) where
    impBackwardPTA (impls, _) while post = impBackwardPT impls while post

instance ImpBackwardPTA (FunImplEnv, FunSpecEnv) (ImpCall e) where
  impBackwardPTA (impls, specs) (ImpCall cid args assignees) post =
    case (Map.lookup cid impls, Map.lookup cid specs) of
      (Nothing, Nothing) ->
        throwError $ "No implementation or specification for " ++ cid
      (Just impl, _) -> impBackwardPT impls (ImpCall cid args assignees) post
      (_, Just spec) -> do
        (cvars, fPre, fPost) <- specAtCallsite spec args
        let retVars  = returnVars $ length assignees
        frAssignees <- envFreshen assignees
        let frPost   = substituteAll assignees frAssignees post
        let frFPost  = substituteAll retVars   frAssignees fPost
        return $ And [fPre, Imp frFPost frPost]

instance (ImpBackwardPTA c (f e), ImpBackwardPTA c (g e)) =>
  ImpBackwardPTA c ((f :+: g) e) where
    impBackwardPTA ctx (Inl f) post = impBackwardPTA ctx f post
    impBackwardPTA ctx (Inl g) post = impBackwardPTA ctx g post

instance ImpBackwardPTA (FunImplEnv, FunSpecEnv) FunImpProgram where
  impBackwardPTA ctx (In f) post = impBackwardPTA ctx f post


-----------------------------------------------
-- Backward Predicate Transform: Existential --
-----------------------------------------------

class ImpBackwardPTE c p where
  impBackwardPTE :: c -> p -> Assertion -> Ceili Assertion

instance ImpBackwardPTE (FunImplEnv, FunSpecEnv) (ImpCall e) where
  impBackwardPTE (impls, specs) (ImpCall cid args assignees) post =
    case (Map.lookup cid impls, Map.lookup cid specs) of
      (Nothing, Nothing) ->
        throwError $ "No implementation or specification for " ++ cid
      (Just impl, _) -> impBackwardPT impls (ImpCall cid args assignees) post
      (_, Just spec) -> do
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


instance ImpBackwardPTE (FunImplEnv, FunSpecEnv) FunImpProgram where
  impBackwardPTE ctx (In f) post = impBackwardPTE ctx f post


---------------
-- Utilities --
---------------

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
