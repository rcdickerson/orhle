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
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , LoopHeadStates
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
import Ceili.Evaluation
import Ceili.Language.AExp
import Ceili.Language.Compose
import Ceili.Language.FunImp
import Ceili.Literal
import Ceili.Name
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.SMTString
import Ceili.StatePredicate
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
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
  } deriving Show

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

instance Ord t => CollectableLiterals (SpecCall t e) t where
  litsIn (SpecCall _ args _) = litsIn args


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

instance Ord t => CollectableLiterals (SpecImpProgram t) t where
  litsIn (In f) = litsIn f

specCall :: (SpecCall t :<: f) => CallId -> [AExp t] -> [Name] -> ImpExpr t f
specCall cid args assignees = inject $ SpecCall cid args assignees

toImpCall :: SpecCall t e -> ImpCall t e
toImpCall (SpecCall cid args assignees) = ImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

data SpecImpEvalContext t e = SpecImpEvalContext { siec_fuel  :: Fuel
                                                 , siec_env   :: SpecImpEnv t e
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

instance ( Num t
         , SMTString t
         , SMTTypeString t
         , AssertionParseable t
         , Evaluable (SpecImpEvalContext t e) t (AExp t) t
         , Evaluable (SpecImpEvalContext t e) t e (ImpStep t)
         ) => Evaluable (SpecImpEvalContext t e) t (SpecCall t e) (ImpStep t) where
  eval ctx st call =
    let
      env = siec_env ctx
      cid = sc_callId call
    in case (Map.lookup cid $ sie_impls env,
             Map.lookup cid $ sie_qspecs env SIQ_Universal,
             Map.lookup cid $ sie_qspecs env SIQ_Existential) of
      (Just _, _, _)     -> eval ctx st (toImpCall call)
      (_, Just aspec, _) -> evalSpec st aspec call
      (_, _, Just espec) -> evalSpec st espec call
      _ -> throwError $ "No implementation or specification for " ++ cid

evalSpec :: ( Num t
            , SMTString t
            , SMTTypeString t
            , AssertionParseable t
            )
         => ProgState t
         -> Specification t
         -> SpecCall t e
         -> Ceili (Maybe (ProgState t))
evalSpec st
         spec@(Specification params retVars choiceVars specPre specPost)
         call@(SpecCall _ args assignees) =
  do
    checkArglists spec call
    let callsitePre  = assertionAtState st
                     $ instantiateParams params args specPre
    let callsitePost = substituteAll retVars assignees
                     $ assertionAtState st
                     $ instantiateParams params args specPost
    let query = case choiceVars of
          [] -> And [callsitePre, callsitePost]
          _  -> Exists choiceVars $ And [callsitePre, callsitePost]
    sat <- checkSatWithLog LogLevelNone query
    case sat of
      SMT.SatUnknown -> do
        log_e "[SpecImpEval] Spec call query sat unknown"
        return Nothing
      SMT.Unsat -> do
        log_e "[SpecImpEval] Spec call unsat"
        return Nothing
      SMT.Sat model -> do
        let assigneeSt = Map.filterWithKey (\k -> \_ -> k `elem` assignees) (modelToState model)
        return $ Just $ Map.union assigneeSt st

-- TODO: This is janky.
modelToState :: ( Num t
                , SMTString t
                , SMTTypeString t
                , AssertionParseable t
                )
             => String
             -> ProgState t
modelToState modelStr = case parseAssertion modelStr of
  Left err -> error $ "Parse error: " ++ show err
  Right assertion -> extractState assertion
  where
    extractState assertion = case assertion of
      Eq lhs rhs -> Map.fromList [(extractName lhs, extractInt rhs)]
      And as     -> Map.unions $ map extractState as
      _ -> error $ "Unexpected assertion in SAT model: " ++ show assertion
    extractName arith = case arith of
      Var name -> name
      _ -> error $ "Unexpected arith in SAT model (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      Sub [Num n] -> -n
      _ -> error $ "Unexpected arith in SAT model (expected int): " ++ show arith


-- TODO: Evaluating a function call should cost fuel to prevent infinite recursion.

instance ( Num t
         , SMTString t
         , SMTTypeString t
         , AssertionParseable t
         , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (AExp t) t
         , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (BExp t) Bool
         ) => Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (SpecImpProgram t) (ImpStep t) where
  eval ctx st (In f) = eval ctx st f


-----------------
-- Test States --
-----------------

instance CollectLoopHeadStates (SpecImpEvalContext t e) (SpecCall t e) t where
  collectLoopHeadStates _ _ _ = return Map.empty

instance ( Num t
         , Ord t
         , SMTString t
         , SMTTypeString t
         , AssertionParseable t
         , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (AExp t) t
         , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (BExp t) Bool
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

data SpecImpPTSContext t e = SpecImpPTSContext { fipc_quant          :: SpecImpQuant
                                               , fipc_specEnv        :: SpecImpEnv t e
                                               , fipc_loopHeadStates :: LoopHeadStates t
                                               , fipc_programNames   :: Set Name
                                               , fipc_programLits    :: Set t
                                               }

instance FunImplLookup (SpecImpPTSContext t (SpecImpProgram t)) (SpecImpProgram t) where
  lookupFunImpl ctx = lookupFunImpl (sie_impls . fipc_specEnv $ ctx)

instance ImpPieContextProvider (SpecImpPTSContext t (SpecImpProgram t)) t where
  impPieCtx ctx = ImpPieContext
    { pc_loopHeadStates = fipc_loopHeadStates ctx
    , pc_programNames   = fipc_programNames ctx
    , pc_programLits    = fipc_programLits ctx
    }

class SpecImpEnvProvider a t e where
  getSpecImpEnv :: a -> SpecImpEnv t e
instance SpecImpEnvProvider (SpecImpPTSContext t e) t e where
  getSpecImpEnv = fipc_specEnv

class SpecImpQuantProvider a where
  getSpecImpQuant :: a -> SpecImpQuant
instance SpecImpQuantProvider (SpecImpPTSContext t e) where
  getSpecImpQuant = fipc_quant

instance ( Num t
         , Ord t
         , SMTString t
         , SMTTypeString t
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
