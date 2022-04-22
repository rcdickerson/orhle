{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Orhle.SpecImp
  ( AExp(..)
  , BExp(..)
  , CallId
  , CollectLoopHeadStates(..)
  , Fuel(..)
  , FuelTank(..)
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
  , ImpStep
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , LoopHeadStates
  , MapImpType(..)
  , Name(..)
  , SpecCall(..)
  , SpecImpEnv(..)
  , SpecImpEvalContext(..)
  , SpecImpProgram
  , SpecImpPTSContext(..)
  , SpecImpQuant(..)
  , SpecImpQuantProvider(..)
  , Specification(..)
  , SpecMap
  , SplitOnBExp(..)
  , impAsgn
  , impCall
  , impIf
  , impSeq
  , impSkip
  , impWhile
  , impWhileWithMeta
  , mapLoopHeadStates
  , mapSpecEnvType
  , mapSpecImpEnvType
  , populateLoopIds
  , repopulateLoopIds
  , specCall
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Evaluation
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Language.FunImp
import Ceili.Literal
import Ceili.Name
import Ceili.ProgState
import Ceili.StatePredicate
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.UUID
import qualified Data.UUID.V4 as UUID
import Prettyprinter


--------------------
-- Specifications --
--------------------

data Specification t = Specification
  { spec_params        :: [Name]
  , spec_returnVars    :: [Name]
  , spec_choiceVars    :: [Name]
  , spec_preCondition  :: Assertion t
  , spec_postCondition :: Assertion t
  } deriving (Show, Functor)

instance CollectableNames (Specification t) where
  namesIn (Specification ps rets cs pre post) = Set.unions allNames
    where
      allNames = [ Set.fromList ps
                 , namesIn rets
                 , Set.unions $ map namesIn cs
                 , namesIn pre
                 , namesIn post ]

instance MappableNames (Specification t) where
  mapNames f (Specification ps rets cs pre post) =
    Specification (mapNames f ps)
                  (mapNames f rets)
                  (mapNames f cs)
                  (mapNames f pre)
                  (mapNames f post)

instance Ord t => CollectableLiterals (Specification t) t where
  litsIn (Specification _ _ _ pre post) = Set.union (litsIn pre) (litsIn post)


-------------------------------
-- Specification Environment --
-------------------------------

type SpecMap t    = Map Handle (Specification t)
data SpecImpQuant = SIQ_Universal | SIQ_Existential
data FunSpecEnv t = FunSpecEnv { fse_aspecs :: SpecMap t
                               , fse_especs :: SpecMap t }

instance CollectableNames (FunSpecEnv t) where
  namesIn (FunSpecEnv aspecs especs) =
    Set.unions [ Set.unions $ map namesIn (Map.elems aspecs)
               , Set.unions $ map namesIn (Map.elems especs) ]

instance Ord t => CollectableLiterals (FunSpecEnv t) t where
  litsIn (FunSpecEnv aspecs especs) =
    Set.union (litsIn $ Map.elems aspecs)
              (litsIn $ Map.elems especs)

mapSpecEnvType :: (t -> t') -> FunSpecEnv t -> FunSpecEnv t'
mapSpecEnvType f (FunSpecEnv aspecs especs) = FunSpecEnv (Map.map (fmap f) aspecs)
                                                         (Map.map (fmap f) especs)

fse_qspecs :: FunSpecEnv t -> SpecImpQuant -> SpecMap t
fse_qspecs env quant = case quant of
  SIQ_Universal   -> fse_aspecs env
  SIQ_Existential -> fse_especs env


---------------------------------------------------------
-- Combined Specification + Implementation Environment --
---------------------------------------------------------

data SpecImpEnv t e = SpecImpEnv { sie_impls :: FunImplEnv e
                                 , sie_specs :: FunSpecEnv t
                                 }

instance CollectableNames e => CollectableNames (SpecImpEnv t e) where
  namesIn (SpecImpEnv impls specs) = Set.union (namesIn impls) (namesIn specs)

instance (Ord t, CollectableLiterals e t) => CollectableLiterals (SpecImpEnv t e) t where
  litsIn (SpecImpEnv impls specs) =
    Set.union (litsIn $ Map.elems impls) (litsIn specs)

mapSpecImpEnvType :: MapImpType t t' implT implT'
                  => (t -> t')
                  -> SpecImpEnv t implT
                  -> SpecImpEnv t' implT'
mapSpecImpEnvType f (SpecImpEnv impls specs) =
  let
    impls' = Map.map (fmap $ mapImpType f) impls
    specs' = mapSpecEnvType f specs
  in SpecImpEnv impls' specs'

sie_qspecs :: SpecImpEnv t e -> SpecImpQuant -> SpecMap t
sie_qspecs = fse_qspecs . sie_specs


--------------------
-- Function Calls --
--------------------

-- Structurally identical to FunImp's ImpCall, but
-- we will give it a different predicate transform
-- semantics which looks for either an implementation
-- or a specification.

data SpecCall t e = SpecCall { sc_callId    :: CallId
                             , sc_args      :: [AExp t]
                             , sc_assignees :: [Name]
                             }
  deriving (Eq, Ord, Show, Functor)

instance CollectableNames (SpecCall t e) where
  namesIn (SpecCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance FreshableNames (SpecCall t e) where
  freshen (SpecCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ SpecCall cid args' assignees'

instance MappableNames (SpecCall t e) where
  mapNames f (SpecCall cid args assignees) =
    SpecCall cid (map (mapNames f) args) (map f assignees)

instance TransformMetadata m e t => TransformMetadata m (SpecCall t e) t where
  transformMetadata call _ = return call

instance Ord t => CollectableLiterals (SpecCall t e) t where
  litsIn (SpecCall _ args _) = litsIn args

instance MapImpType t t' (SpecCall t e) (SpecCall t' e') where
  mapImpType f (SpecCall callId args assignees) = SpecCall callId (map (fmap f) args) assignees


---------------------
-- SpecImp Language --
---------------------

type SpecImpProgram t = ImpExpr t ( SpecCall t
                                :+: ImpSkip t
                                :+: ImpAsgn t
                                :+: ImpSeq t
                                :+: ImpIf t
                                :+: ImpWhile t )

instance CollectableNames (SpecImpProgram t) where
  namesIn (In f) = namesIn f

instance MappableNames (SpecImpProgram t) where
  mapNames func (In f) = In $ mapNames func f

instance FreshableNames (SpecImpProgram t) where
  freshen (In f) = return . In =<< freshen f

instance Monad m => TransformMetadata m (SpecImpProgram t) t where
  transformMetadata (In prog) func = do
    prog' <- transformMetadata prog func
    return $ In prog'

instance Ord t => CollectableLiterals (SpecImpProgram t) t where
  litsIn (In f) = litsIn f

instance MapImpType t t' (SpecImpProgram t) (SpecImpProgram t') where
  mapImpType f (In p) = In $ mapImpType f p

specCall :: (SpecCall t :<: f) => CallId -> [AExp t] -> [Name] -> ImpExpr t f
specCall cid args assignees = inject $ SpecCall cid args assignees

toImpCall :: SpecCall t e -> ImpCall t e
toImpCall (SpecCall cid args assignees) = ImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

data SpecImpEvalContext t e = SpecImpEvalContext { siec_fuel :: Fuel
                                                 , siec_env  :: SpecImpEnv t e
                                                 }

instance FuelTank (SpecImpEvalContext t e) where
  getFuel = siec_fuel
  setFuel (SpecImpEvalContext _ env) fuel = SpecImpEvalContext fuel env

instance FunImplLookup (SpecImpEvalContext t e) e where
  lookupFunImpl ctx name =
    let impls = (sie_impls . siec_env) ctx
    in case Map.lookup name impls of
      Nothing   -> throwError $ "No implementation for " ++ name
      Just impl -> return impl

instance ( Embeddable Integer t
         , AssertionParseable t
         , SplitOnBExp t
         , Evaluable (SpecImpEvalContext t e) t (AExp t) t
         , Evaluable (SpecImpEvalContext t e) t e (ImpStep t)
         , Evaluable () t (SpecImpQuant, Specification t, SpecCall t e) (ImpStep t)
         ) => Evaluable (SpecImpEvalContext t e) t (SpecCall t e) (ImpStep t) where
  eval ctx st call =
    let
      env = siec_env ctx
      cid = sc_callId call
      evalSpec = eval @() @t @(SpecImpQuant, Specification t, SpecCall t e)
    in case (Map.lookup cid $ sie_impls env,
             Map.lookup cid $ sie_qspecs env SIQ_Universal,
             Map.lookup cid $ sie_qspecs env SIQ_Existential) of
      (Just _, _, _)     -> eval ctx st (toImpCall call)
      (_, Just aspec, _) -> evalSpec () st (SIQ_Universal, aspec, call)
      (_, _, Just espec) -> evalSpec () st (SIQ_Existential, espec, call)
      _ -> throwError $ "No implementation or specification for " ++ cid

-- TODO: Evaluating a function call should cost fuel to prevent infinite recursion.

instance ( Embeddable Integer t
         , AssertionParseable t
         , AExpAlgebra t
         , SplitOnBExp t
         , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (AExp t) t
         , Evaluable () t (SpecImpQuant, Specification t, SpecCall t (SpecImpProgram t)) (ImpStep t)
         ) => Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (SpecImpProgram t) (ImpStep t) where
  eval ctx st (In f) = eval ctx st f


-----------------
-- Test States --
-----------------

instance CollectLoopHeadStates (SpecImpEvalContext t e) (SpecCall t e) t where
  collectLoopHeadStates _ _ _ = return Map.empty

instance ( Embeddable Integer t
         , Ord t
         , AExpAlgebra t
         , SplitOnBExp t
         , AssertionParseable t
         , Evaluable () t (SpecImpQuant, Specification t, SpecCall t (SpecImpProgram t)) (ImpStep t)
         ) => CollectLoopHeadStates (SpecImpEvalContext t (SpecImpProgram t)) (SpecImpProgram t) t where
  collectLoopHeadStates ctx sts (In f) = collectLoopHeadStates ctx sts f


--------------------
-- Pretty Printer --
--------------------

instance Pretty t => Pretty (SpecCall t e) where
  pretty (SpecCall callId args assignees) =
    prettyAssignees assignees <+> pretty ":=" <+> pretty callId <> prettyArgs args

instance Pretty t => Pretty (SpecImpProgram t) where
  pretty (In p) = pretty p


---------------
-- Utilities --
---------------

class GetLoop t e where
  getLoop :: e -> Maybe (ImpWhile t (SpecImpProgram t))
instance (GetLoop t (f e), GetLoop t (g e)) => GetLoop t ((f :+: g) e) where
  getLoop (Inl f) = getLoop f
  getLoop (Inr g) = getLoop g
instance GetLoop t (SpecImpProgram t) where
  getLoop (In p) = getLoop p
instance GetLoop t (ImpSkip t e)  where getLoop _ = Nothing
instance GetLoop t (ImpAsgn t e)  where getLoop _ = Nothing
instance GetLoop t (ImpSeq t e)   where getLoop _ = Nothing
instance GetLoop t (ImpIf t e)    where getLoop _ = Nothing
instance GetLoop t (ImpCall t e)  where getLoop _ = Nothing
instance GetLoop t (SpecCall t e) where getLoop _ = Nothing
instance GetLoop t (ImpWhile t (SpecImpProgram t)) where getLoop = Just


----------------------------------
-- Backward Predicate Transform --
----------------------------------

data SpecImpPTSContext t e = SpecImpPTSContext { sipc_quant            :: SpecImpQuant
                                               , sipc_specEnv          :: SpecImpEnv t e
                                               , sipc_loopHeadStates   :: LoopHeadStates t
                                               , sipc_programNames     :: Set Name
                                               , sipc_programLits      :: Set t
                                               }

instance FunImplLookup (SpecImpPTSContext t (SpecImpProgram t)) (SpecImpProgram t) where
  lookupFunImpl ctx = lookupFunImpl (sie_impls . sipc_specEnv $ ctx)

instance ImpPieContextProvider (SpecImpPTSContext t (SpecImpProgram t)) t where
  impPieCtx ctx = ImpPieContext
    { pc_loopHeadStates = sipc_loopHeadStates ctx
    , pc_programNames   = sipc_programNames ctx
    , pc_programLits    = sipc_programLits ctx
    }

class SpecImpEnvProvider a t e where
  getSpecImpEnv :: a -> SpecImpEnv t e
instance SpecImpEnvProvider (SpecImpPTSContext t e) t e where
  getSpecImpEnv = sipc_specEnv

class SpecImpQuantProvider a where
  getSpecImpQuant :: a -> SpecImpQuant
instance SpecImpQuantProvider (SpecImpPTSContext t e) where
  getSpecImpQuant = sipc_quant

instance ( Embeddable Integer t
         , ValidCheckable t
         , Pretty t
         , Ord t
         , AssertionParseable t
         , SpecImpQuantProvider c
         , SpecImpEnvProvider c t (SpecImpProgram t)
         , FunImplLookup c (SpecImpProgram t)
         , StatePredicate (Assertion t) t
         , ImpPieContextProvider c t
         ) => ImpBackwardPT c (SpecImpProgram t) t where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post

instance ( ImpBackwardPT c e t
         , SpecImpQuantProvider c
         , SpecImpEnvProvider c t e
         , FunImplLookup c e
         , FreshableNames e )
         => ImpBackwardPT c (SpecCall t e) t where
  impBackwardPT ctx call post =
    let cid     = sc_callId call
        quant   = getSpecImpQuant ctx
        specEnv = getSpecImpEnv @c @t @e ctx
    in case ( Map.lookup cid $ sie_impls specEnv
            , Map.lookup cid $ sie_qspecs specEnv quant) of
      (Nothing, Nothing) ->
        throwError $ "No implementation or specification for " ++ cid
      (Just _, _) ->
        impBackwardPT ctx (toImpCall call) post
      (_, Just spec) ->
        case quant of
          SIQ_Universal   -> universalSpecPT spec call post
          SIQ_Existential -> existentialSpecPT spec call post

universalSpecPT :: Specification t -> (SpecCall t e) -> Assertion t -> Ceili (Assertion t)
universalSpecPT spec@(Specification params retVars _ specPre specPost)
                call@(SpecCall _ args assignees)
                post =
  do
    checkArglists spec call
    freshAssignees  <- envFreshen assignees
    let callsitePre  = instantiateParams params args specPre
    let callsitePost = substituteAll retVars freshAssignees
                     $ instantiateParams params args specPost
    let sitePost = substituteAll assignees freshAssignees post
    return $ And [ callsitePre
                 , Forall freshAssignees $ Imp callsitePost sitePost
                 ]

existentialSpecPT :: Specification t -> (SpecCall t e) -> Assertion t -> Ceili (Assertion t)
existentialSpecPT spec@(Specification params retVars choiceVars specPre specPost)
                  call@(SpecCall _ args assignees)
                  post =
  do
    checkArglists spec call
    freshChoiceVars <- envFreshen choiceVars
    freshAssignees  <- envFreshen assignees
    let callsitePre  = substituteAll choiceVars freshChoiceVars
                     $ instantiateParams params args specPre
    let callsitePost = substituteAll choiceVars freshChoiceVars
                     $ substituteAll retVars freshAssignees
                     $ instantiateParams params args specPost
    let sitePost = substituteAll assignees freshAssignees post
    let wp = And [ callsitePre
                 , Exists (freshAssignees) callsitePost
                 , Forall (freshAssignees) $ Imp callsitePost sitePost
                 ]
    return $ case choiceVars of
      [] -> wp
      _  -> Exists freshChoiceVars wp


checkArglists :: Specification t -> (SpecCall t e) -> Ceili ()
checkArglists (Specification params retVars _ _ _) (SpecCall _ args assignees) =
  if      length args /= length params then throwError "Argument / parameter length mismatch"
  else if length assignees /= length retVars then throwError "Assignees / returns length mismatch"
  else return ()

instantiateParams :: SubstitutableArith t a => [Name] -> [AExp t] -> a -> a
instantiateParams params args a =
  let
    toAriths  = map aexpToArith args
  in foldr (uncurry subArith) a (zip params toAriths)
