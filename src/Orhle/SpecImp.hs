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
  , spec_returnVars    :: [Name]
  , spec_choiceVars    :: [TypedName]
  , spec_preCondition  :: Assertion
  , spec_postCondition :: Assertion
  } deriving Show

instance CollectableNames Specification where
  namesIn (Specification ps rets cs pre post) = Set.unions allNames
    where
      allNames = [ Set.fromList ps
                 , namesIn rets
                 , Set.unions $ map namesIn cs
                 , namesIn pre
                 , namesIn post ]

instance MappableNames Specification where
  mapNames f (Specification ps rets cs pre post) =
    Specification (mapNames f ps)
                  (mapNames f rets)
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
universalSpecPT spec call post = do
  (_, callsitePre, callsitePost) <- specAtCallsite call spec
  return $ And [callsitePre, Imp callsitePost post]

existentialSpecPT :: Specification -> (SpecCall e) -> Assertion -> Ceili Assertion
existentialSpecPT spec call post = do
  (choiceVars, callsitePre, callsitePost) <- specAtCallsite call spec
  let tnAssignees = map (\n -> TypedName n Int) (sc_assignees call)
      existsPost = Exists tnAssignees callsitePost
      forallPost = Forall tnAssignees $ Imp callsitePost post
  return $ case (length choiceVars) of
    0 -> And [callsitePre, existsPost, forallPost]
    _ -> Exists choiceVars $ And [callsitePre, existsPost, forallPost]

specAtCallsite :: SpecCall e -> Specification -> Ceili ([TypedName], Assertion, Assertion)
specAtCallsite (SpecCall _ args assignees) (Specification params retVars choiceVars pre post) =
  if      length args /= length params       then throwError "Argument / parameter length mismatch"
  else if length assignees /= length retVars then throwError "Assignees / returns length mismatch"
  else do
    freshChoiceVars <- envFreshen choiceVars
    let subCallsite = (instantiateParams params args) .
                      (substituteAll retVars assignees)
    let callsitePre = subCallsite pre
    let callsitePost = subCallsite post
    return (freshChoiceVars, callsitePre, callsitePost)

instantiateParams :: SubstitutableArith a => [Name] -> [AExp] -> a -> a
instantiateParams params args a =
  let
    fromNames = map (\n -> TypedName n Int) params
    toAriths  = map aexpToArith args
  in foldr (uncurry subArith) a (zip fromNames toAriths)
