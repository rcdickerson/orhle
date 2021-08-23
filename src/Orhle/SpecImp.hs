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
  , PopulateTestStates(..)
  , SpecCall(..)
  , SpecImpEnv(..)
  , SpecImpEvalContext(..)
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
import Ceili.Literal
import Ceili.Name
import qualified Ceili.SMT as SMT
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prettyprinter


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

instance CollectableTypedNames Specification where
  typedNamesIn spec = Set.map (\n -> TypedName n Int) $ namesIn spec

instance MappableNames Specification where
  mapNames f (Specification ps rets cs pre post) =
    Specification (mapNames f ps)
                  (mapNames f rets)
                  (mapNames f cs)
                  (mapNames f pre)
                  (mapNames f post)

instance CollectableLiterals Specification where
  litsIn (Specification _ _ _ pre post) = Set.union (litsIn pre) (litsIn post)

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

instance CollectableTypedNames FunSpecEnv where
  typedNamesIn spec = Set.map (\n -> TypedName n Int) $ namesIn spec

instance CollectableLiterals FunSpecEnv where
  litsIn (FunSpecEnv aspecs especs) =
    Set.union (litsIn $ Map.elems aspecs)
              (litsIn $ Map.elems especs)

fse_qspecs :: FunSpecEnv -> SpecImpQuant -> SpecMap
fse_qspecs env quant = case quant of
  SIQ_Universal   -> fse_aspecs env
  SIQ_Existential -> fse_especs env


---------------------------------------------------------
-- Combined Specification + Implementation Environment --
---------------------------------------------------------

data SpecImpEnv e = SpecImpEnv { sie_impls :: FunImplEnv e
                               , sie_specs :: FunSpecEnv
                               }

instance CollectableNames e => CollectableNames (SpecImpEnv e) where
  namesIn (SpecImpEnv impls specs) = Set.union (namesIn impls) (namesIn specs)

instance CollectableTypedNames e => CollectableTypedNames (SpecImpEnv e) where
  typedNamesIn (SpecImpEnv impls specs) =
    Set.union (typedNamesIn $ Map.elems impls) (typedNamesIn specs)

instance CollectableLiterals e => CollectableLiterals (SpecImpEnv e) where
  litsIn (SpecImpEnv impls specs) =
    Set.union (litsIn $ Map.elems impls) (litsIn specs)

sie_qspecs :: SpecImpEnv e -> SpecImpQuant -> SpecMap
sie_qspecs = fse_qspecs . sie_specs


--------------------
-- Function Calls --
--------------------

-- Structurally identical to FunImp's ImpCall, but
-- we will give it a different predicate transform
-- semantics which looks for either an implementation
-- or a specification.

data SpecCall e = SpecCall { sc_callId    :: CallId
                           , sc_args      :: [AExp]
                           , sc_assignees :: [Name]
                           }
  deriving (Eq, Ord, Show, Functor)

instance CollectableNames (SpecCall e) where
  namesIn (SpecCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance CollectableTypedNames (SpecCall e) where
  typedNamesIn (SpecCall _ args assignees) =
    Set.union (typedNamesIn args)
              (Set.fromList $ map (\n -> TypedName n Int) assignees)

instance FreshableNames (SpecCall e) where
  freshen (SpecCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ SpecCall cid args' assignees'

instance MappableNames (SpecCall e) where
  mapNames f (SpecCall cid args assignees) =
    SpecCall cid (map (mapNames f) args) (map f assignees)

instance CollectableLiterals (SpecCall e) where
  litsIn (SpecCall _ args _) = litsIn args


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

instance CollectableTypedNames SpecImpProgram where
  typedNamesIn (In f) = typedNamesIn f

instance MappableNames SpecImpProgram where
  mapNames func (In f) = In $ mapNames func f

instance FreshableNames SpecImpProgram where
  freshen (In f) = return . In =<< freshen f

instance CollectableLiterals SpecImpProgram where
  litsIn (In f) = litsIn f

specCall :: (SpecCall :<: f) => CallId -> [AExp] -> [Name] -> ImpExpr f
specCall cid args assignees = inject $ SpecCall cid args assignees

toImpCall :: SpecCall e -> ImpCall e
toImpCall (SpecCall cid args assignees) = ImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

data SpecImpEvalContext e = SpecImpEvalContext { siec_fuel  :: Fuel
                                               , siec_env   :: SpecImpEnv e
                                               }

instance FuelTank (SpecImpEvalContext e) where
  getFuel = siec_fuel
  setFuel (SpecImpEvalContext _ env) fuel = SpecImpEvalContext fuel env

instance FunImplLookup (SpecImpEvalContext e) e where
  lookupFunImpl ctx name =
    let impls = (sie_impls . siec_env) ctx
    in case Map.lookup name impls of
      Nothing   -> throwError $ "No implementation for " ++ name
      Just impl -> return impl

instance EvalImp (SpecImpEvalContext e) e => EvalImp (SpecImpEvalContext e) (SpecCall e) where
  evalImp ctx st call =
    let
      env = siec_env ctx
      cid = sc_callId call
    in case (Map.lookup cid $ sie_impls env,
             Map.lookup cid $ sie_qspecs env SIQ_Universal,
             Map.lookup cid $ sie_qspecs env SIQ_Existential) of
      (Just _, _, _)     -> evalImp ctx st (toImpCall call)
      (_, Just aspec, _) -> evalSpec st aspec call
      (_, _, Just espec) -> evalSpec st espec call
      _ -> throwError $ "No implementation or specification for " ++ cid

evalSpec :: State -> Specification -> SpecCall e -> Ceili (Maybe State)
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
modelToState :: String -> State
modelToState modelStr = case parseAssertion modelStr of
  Left err -> error $ "Parse error: " ++ show err
  Right assertion -> extractState assertion
  where
    extractState assertion = case assertion of
      Eq lhs rhs -> Map.fromList [(extractName lhs, extractInt rhs)]
      And as     -> Map.unions $ map extractState as
      _ -> error $ "Unexpected assertion in SAT model: " ++ show assertion
    extractName arith = case arith of
      Var (TypedName name _) -> name
      _ -> error $ "Unexpected arith in SAT model (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      Sub [Num n] -> -n
      _ -> error $ "Unexpected arith in SAT model (expected int): " ++ show arith


-- TODO: Evaluating a function call should cost fuel to prevent infinite recursion.

instance EvalImp (SpecImpEvalContext SpecImpProgram) SpecImpProgram where
  evalImp ctx st (In f) = evalImp ctx st f


-----------------
-- Test States --
-----------------

instance EvalImp (SpecImpEvalContext e) e => PopulateTestStates (SpecImpEvalContext e) (SpecCall e) where
  populateTestStates _ _ = return . id

instance PopulateTestStates (SpecImpEvalContext SpecImpProgram) SpecImpProgram where
  populateTestStates ctx sts (In f) = populateTestStates ctx sts f >>= return . In


--------------------
-- Pretty Printer --
--------------------

instance Pretty (SpecCall e) where
  pretty (SpecCall callId args assignees) =
    prettyAssignees assignees <+> pretty ":=" <+> pretty callId <> prettyArgs args

instance Pretty SpecImpProgram where
  pretty (In p) = pretty p


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
                 , Forall (intNames freshAssignees) $ Imp callsitePost sitePost
                 ]

existentialSpecPT :: Specification -> (SpecCall e) -> Assertion -> Ceili Assertion
existentialSpecPT spec@(Specification params retVars choiceVars specPre specPost)
                  call@(SpecCall _ args assignees)
                  post =
  do
    checkArglists spec call
    freshChoiceVars <- envFreshen choiceVars
    freshAssignees  <- envFreshen assignees
    let callsitePre  = substituteAll (map tn_name choiceVars) (map tn_name freshChoiceVars)
                     $ instantiateParams params args specPre
    let callsitePost = substituteAll (map tn_name choiceVars) (map tn_name freshChoiceVars)
                     $ substituteAll retVars freshAssignees
                     $ instantiateParams params args specPost
    let sitePost = substituteAll assignees freshAssignees post
    let wp = And [ callsitePre
                 , Exists (intNames freshAssignees) callsitePost
                 , Forall (intNames freshAssignees) $ Imp callsitePost sitePost
                 ]
    return $ case choiceVars of
      [] -> wp
      _  -> Exists freshChoiceVars wp


checkArglists :: Specification -> (SpecCall e) -> Ceili ()
checkArglists (Specification params retVars _ _ _) (SpecCall _ args assignees) =
  if      length args /= length params then throwError "Argument / parameter length mismatch"
  else if length assignees /= length retVars then throwError "Assignees / returns length mismatch"
  else return ()

instantiateParams :: SubstitutableArith a => [Name] -> [AExp] -> a -> a
instantiateParams params args a =
  let
    fromNames = intNames params
    toAriths  = map aexpToArith args
  in foldr (uncurry subArith) a (zip fromNames toAriths)

intNames :: [Name] -> [TypedName]
intNames = map (\n -> TypedName n Int)
