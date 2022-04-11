{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.RelationalPTS
  ( RelSpecImpPTSContext(..)
  , relBackwardPT
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import qualified Ceili.FeatureLearning.LinearInequalities as LI
--import qualified Ceili.InvariantInference.LoopInvGen as Lig
import Ceili.Language.BExp ( bexpToAssertion )
import Ceili.Language.Imp ( IterStateMap )
import Ceili.Name
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Control.Monad.State ( runState )
import Control.Monad.Trans ( lift )
import Data.Maybe ( catMaybes )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Strings ( strSplitAll )
import Data.UUID
--import qualified Orhle.CInvGen as CI
import Orhle.InvGen.OrhleInvGen ( Configuration(..), Job(..) )
import qualified Orhle.InvGen.OrhleInvGen as OIG
import Orhle.FeatureGen (genFeatures, lia)
import Orhle.SpecImp
import Orhle.StepStrategy
import Prettyprinter
import System.Random ( randomRIO )

data RelSpecImpPTSContext t e = RelSpecImpPTSContext { rsipc_specEnv          :: SpecImpEnv t e
                                                     , rsipc_loopHeadStates   :: LoopHeadStates t
                                                     , rsipc_programNames     :: Set Name
                                                     , rsipc_programLits      :: Set t
                                                     }

toSinglePTSContext :: SpecImpQuant -> RelSpecImpPTSContext t e -> SpecImpPTSContext t e
toSinglePTSContext quant (RelSpecImpPTSContext specEnv headStates names lits) =
  SpecImpPTSContext quant specEnv headStates names lits

combineLoopHeadStates :: Ord t => RelSpecImpPTSContext t e -> [UUID] -> [ProgState t]
combineLoopHeadStates ctx uuids =
  let
    headStates = rsipc_loopHeadStates ctx
    findStateMap uuid = Map.findWithDefault Map.empty uuid headStates
  in concat . (map Set.toList) . Map.elems . combineIterStateMaps $ map findStateMap uuids

combineIterStateMaps :: Ord t => [IterStateMap t] -> IterStateMap t
combineIterStateMaps = Map.unionsWith $ \left right ->
  Set.map (uncurry Map.union) $ Set.cartesianProduct left right

relBackwardPT :: ( Embeddable Integer t
                 , Ord t
                 , AssertionParseable t
                 , ValidCheckable t
                 , Pretty t
                 , StatePredicate (Assertion t) t
                 , SatCheckable t
                 )
              => BackwardStepStrategy t
              -> RelSpecImpPTSContext t (SpecImpProgram t)
              -> [SpecImpProgram t]
              -> [SpecImpProgram t]
              -> Assertion t
              -> Ceili (Assertion t)
relBackwardPT stepStrategy ctx aprogs eprogs post =
  relBackwardPT' stepStrategy ctx (ProgramRelation aprogs eprogs) post


relBackwardPT' :: ( Embeddable Integer t
                  , Ord t
                  , Pretty t
                  , AssertionParseable t
                  , ValidCheckable t
                  , SatCheckable t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  )
               => BackwardStepStrategy t
               -> RelSpecImpPTSContext t (SpecImpProgram t)
               -> ProgramRelation t
               -> Assertion t
               -> Ceili (Assertion t)
relBackwardPT' stepStrategy ctx (ProgramRelation aprogs eprogs) post = do
  -- log_d   "[RelationalPTS] --------------------------------"
  -- log_d   "[RelationalPTS] Taking step on:"
  -- log_d $ "[RelationalPTS] Post: " ++ (show $ pretty post)
  -- log_d $ "[RelationalPTS] Universal programs:"
  -- log_d $ show $ indent 16 $ vsep (map (\p -> pretty "--------" <> hardline <> pretty p) aprogs) <> hardline
  -- log_d $ "[RelationalPTS] Existential programs:"
  -- log_d $ show $ indent 16 $ vsep (map (\p -> pretty "--------" <> hardline <> pretty p) eprogs) <> hardline
  Step selection aprogs' eprogs' <- stepStrategy aprogs eprogs
  -- log_d $ "[RelationalPTS] Step: " ++ (show $ pretty selection)
  -- log_d   "[RelationalPTS] --------------------------------"
  case selection of
    NoSelectionFound ->
      case (aprogs', eprogs') of
        ([], []) -> return post
        _ -> throwError "Unable to find step"
    UniversalStatement stmt -> do
      post' <- impBackwardPT (toSinglePTSContext SIQ_Universal ctx) stmt post
      relBackwardPT stepStrategy ctx aprogs' eprogs' post'
    ExistentialStatement stmt -> do
      post' <- impBackwardPT (toSinglePTSContext SIQ_Existential ctx) stmt post
      relBackwardPT stepStrategy ctx aprogs' eprogs' post'
    LoopFusion aloops eloops -> do
      let continueWithInv inv = useInvariant inv stepStrategy ctx aloops eloops aprogs' eprogs' post
      let annotatedInvars = Set.toList . Set.fromList . catMaybes $ (map invar aloops) ++ (map invar eloops)
      case annotatedInvars of
        (_:_) -> continueWithInv (And annotatedInvars)
        []    -> do
          mInvariant <- inferInvariant stepStrategy ctx aloops eloops post
          case mInvariant of
            Just inv -> continueWithInv inv
            Nothing -> do
              log_e "[RelationalPTS] Unable to infer loop invariant, proceeding with False"
              continueWithInv AFalse -- TODO: Fall back to single stepping over loops.

useInvariant :: ( Embeddable Integer t
                , Ord t
                , AssertionParseable t
                , ValidCheckable t
                , SatCheckable t
                , Pretty t
                , StatePredicate (Assertion t) t
                )
             => Assertion t
             -> BackwardStepStrategy t
             -> RelSpecImpPTSContext t (SpecImpProgram t)
             -> [ImpWhile t (SpecImpProgram t)]
             -> [ImpWhile t (SpecImpProgram t)]
             -> [SpecImpProgram t]
             -> [SpecImpProgram t]
             -> Assertion t
             -> Ceili (Assertion t)
useInvariant invariant stepStrategy ctx aloops eloops aprogs' eprogs' post = do
  isSufficient <- checkValid =<< sufficiencyQuery aloops eloops post invariant
  invQuery <- invarianceQuery stepStrategy ctx aloops eloops invariant
  isInvariant  <- checkValid . fst $ invQuery
  --log_d $ "Invariance query: " ++ (show . pretty . fst $ invQuery)
  -- TODO: Lockstep
  case (isSufficient, isInvariant) of
    (SMT.Valid, SMT.Valid) -> do
      relBackwardPT stepStrategy ctx aprogs' eprogs' invariant
    (SMT.Invalid _, _) -> do
      log_e "[RelationalPTS] Invariant is insufficient to establish post"
      return AFalse
    (_, SMT.Invalid _) -> do
      log_e "[RelationalPTS] Invariant is not invariant on loop body or does not decrease measure"
      return AFalse
    (SMT.ValidTimeout, _) -> do
      log_e "[RelationalPTS] SMT solver timed out when determining sufficency to establish post."
      return AFalse
    (SMT.ValidUnknown, _) -> do
      log_e "[RelationalPTS] SMT solver returned unknown when determining sufficency to establish post."
      return AFalse
    (_, SMT.ValidTimeout) -> do
      log_e "[RelationalPTS] SMT solver timed out when determining invariance on loop body."
      return AFalse
    (_, SMT.ValidUnknown) -> do
      log_e "[RelationalPTS] SMT solver returned unknown when determining invariance on loop body."
      return AFalse

sufficiencyQuery :: [ImpWhile t (SpecImpProgram t)]
                 -> [ImpWhile t (SpecImpProgram t)]
                 -> Assertion t
                 -> Assertion t
                 -> Ceili (Assertion t)
sufficiencyQuery aloops eloops post assertion = do
  let conds = map condA (aloops ++ eloops)
  pure $ Imp (aAnd $ assertion:(map Not conds)) post

vacuityQuery :: [ImpWhile t (SpecImpProgram t)]
             -> [ImpWhile t (SpecImpProgram t)]
             -> Assertion t
             -> Assertion t
             -> Ceili (Assertion t)
vacuityQuery aloops eloops post assertion = do
  let conds = map condA (aloops ++ eloops)
  pure $ (aAnd $ assertion:(map Not conds))

data QuerySubstitution = QuerySubstitution [Name] [Name]

invarianceQuery :: ( Embeddable Integer t
                   , Ord t
                   , AssertionParseable t
                   , ValidCheckable t
                   , SatCheckable t
                   , Pretty t
                   , StatePredicate (Assertion t) t
                   )
                => BackwardStepStrategy t
                -> RelSpecImpPTSContext t (SpecImpProgram t)
                -> [ImpWhile t (SpecImpProgram t)]
                -> [ImpWhile t (SpecImpProgram t)]
                -> Assertion t
                -> Ceili (Assertion t, QuerySubstitution)
invarianceQuery stepStrategy ctx aloops eloops invariant = do
{-  let conds = map condA (aloops ++ eloops)
  wpInvar <- relBackwardPT stepStrategy ctx (map body aloops) (map body eloops) invariant
  pure $ (Imp (aAnd $ invariant:conds) wpInvar, QuerySubstitution [] [])
-}
  let conds = map condA (aloops ++ eloops)
  let measures = catMaybes $ map measure (aloops ++ eloops)
  let names = Set.toList . Set.unions $ [ namesIn conds, namesIn invariant, namesIn aloops, namesIn eloops ]
  frNames <- envFreshen names
  let freshMeasures = substituteAll names frNames measures
  let measureConds = map (uncurry Lt) (zip measures freshMeasures)
                  ++ map (Num (embed 0) `Lte`) measures
  wpInvar <- relBackwardPT stepStrategy ctx (map body aloops) (map body eloops) (aAnd $ invariant:measureConds)
  let frWpInvar = substituteAll names frNames wpInvar
  let frConds = substituteAll names frNames $ aAnd (invariant:conds)
  pure $ (Imp frConds frWpInvar, QuerySubstitution frNames names)

-- TODO: This is fragile.
extractState :: Pretty t => [Name] -> [Name] -> Assertion t -> Ceili (ProgState t)
extractState freshNames names assertion = case assertion of
  Eq lhs rhs -> pure $ Map.fromList [(extractName lhs, extractInt rhs)]
  And as     -> pure . Map.unions =<< mapM (extractState freshNames names) as
  _          -> error $ "Unexpected assertion: " ++ show assertion
  where
    extractName arith = case arith of
      Var name -> substituteAll freshNames names name
      _ -> error $ "Unexpected arith (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      _ -> error $ "Unexpected arith (expected int): " ++ show arith

varName :: Name -> String
varName (Name handle tag) = (last $ strSplitAll "!" handle) ++ "!" ++ (show tag)

collectSameNames :: [Name] -> [[Name]]
collectSameNames names =
  let
    addName name nmap = case Map.lookup (varName name) nmap of
                         Nothing  -> Map.insert (varName name) (Set.singleton name) nmap
                         Just set -> Map.insert (varName name) (Set.insert name set) nmap
    nameMap = foldr addName Map.empty names
  in map Set.toList $ filter (\s -> Set.size s > 1) (Map.elems nameMap)

inferInvariant :: ( Embeddable Integer t
                  , Ord t
                  , AssertionParseable t
                  , SatCheckable t
                  , ValidCheckable t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  )
               => BackwardStepStrategy t
               -> RelSpecImpPTSContext t (SpecImpProgram t)
               -> [ImpWhile t (SpecImpProgram t)]
               -> [ImpWhile t (SpecImpProgram t)]
               -> Assertion t
               -> Ceili (Maybe (Assertion t))
inferInvariant stepStrategy ctx aloops eloops post =
  let
    allLoops = aloops ++ eloops
    headStates = combineLoopHeadStates ctx $ catMaybes $ map (iwm_id . impWhile_meta) allLoops
  in case headStates of
    [] -> throwError "Insufficient test head states for while loop, did you run populateTestStates?"
    _  -> do
--      let names = rsipc_programNames ctx
      let anames   = map (\loop -> Set.intersection (rsipc_programNames ctx) (namesIn loop)) aloops
      let enames   = map (\loop -> Set.intersection (rsipc_programNames ctx) (namesIn loop)) eloops
      let lits     = Set.union (rsipc_programLits ctx) (Set.fromList $ map embed [-1, 0, 1])

      let lis size = Set.fromList $
                     (concat $ map (\names -> genFeatures lia (Set.toList lits) names size) (collectSameNames . Set.toList . Set.unions $ anames ++ enames))
                  ++ (concat $ map (\names -> genFeatures lia (Set.toList lits) (Set.toList names) size) anames)
                  ++ (concat $ map (\names -> genFeatures lia (Set.toList lits) (Set.toList names) size) enames)

--      let lis = Set.fromList $ genFeatures lia (Set.toList lits) (Set.toList $ Set.union anames enames)

--      let lis   = LI.linearInequalities (Set.map embed lits) (Set.unions $ anames ++ enames)

      -- let lis _ = Set.fromList [ Lte (Var $ Name "test!1!counter" 0) (Num $ embed @Integer 5)
      --                          , Lte (Var $ Name "test!2!counter" 0) (Num $ embed @Integer 5)
      --                          , Gte (Var $ Name "test!1!lastTime" 0) (Num $ embed @Integer 0)
      --                          , Gte (Var $ Name "test!2!lastTime" 0) (Num $ embed @Integer 0)
      --                          , Eq (Sub [Var $ Name "test!1!currentTime" 0, Var $ Name "test!1!lastTime" 0]) (Num $ embed @Integer 100)
      --                          , Eq (Sub [Var $ Name "test!2!currentTime" 0, Var $ Name "test!2!lastTime" 0]) (Num $ embed @Integer 101)
      --                          , Eq (Var $ Name "test!1!currentTotal" 0) (Mul [Num $ embed @Integer 100, (Var $ Name "test!1!counter" 0)])
      --                          , Eq (Var $ Name "test!2!currentTotal" 0) (Mul [Num $ embed @Integer 101, (Var $ Name "test!2!counter" 0)])
      --                          ]

      someHeadStates <- lift . lift $ randomSample 5 headStates
      let loopConds = map condA (aloops ++ eloops)
      -- let sufficiency candidate = do
      --       isSufficient <- sufficiencyQuery aloops eloops post candidate
      --       pure $ CI.CandidateQuery isSufficient (pure . id) (extractState [] [])
      -- let invariance candidate = do
      --       (isInvariant, QuerySubstitution freshNames origNames)
      --           <- invarianceQuery stepStrategy ctx aloops eloops candidate
      --       pure $ CI.CandidateQuery isInvariant (pure . substituteAll origNames freshNames) (extractState freshNames origNames)
      -- let vacuity candidate = do
      --       isNonVacuous <- vacuityQuery aloops eloops post candidate
      --       pure $ CI.CandidateQuery isNonVacuous (pure . id) (extractState [] [])
      let oigConfig = Configuration { cfgMaxFeatureSize   = 2
                                    , cfgMaxClauseSize    = 6
                                    , cfgFeatureGenerator = lis
                                    , cfgWpSemantics      = relBackwardPT' stepStrategy
                                    , cfgWpContext        = ctx
                                   }
      let oigJob    = Job { jobBadStates          = []
                          , jobConcreteGoodStates = [ Map.fromList [ (Name "original!sum" 0, embed 101)
                                                                   , (Name "refinement!sum" 0, embed 101)
                                                                   ]
                                                    ]
                          , jobAbstractGoodStates = someHeadStates
                          , jobLoopConds          = loopConds
                          , jobPost               = post
                          }
      OIG.orhleInvGen oigConfig oigJob

body :: ImpWhile t e -> e
body (ImpWhile _ b _) = b

condA :: ImpWhile t e -> Assertion t
condA (ImpWhile c _ _) = bexpToAssertion c

invar :: ImpWhile t e -> Maybe (Assertion t)
invar (ImpWhile _ _ meta) = iwm_invariant meta

measure :: ImpWhile t e -> Maybe (Arith t)
measure (ImpWhile _ _ meta) = iwm_measure meta


-- Adapted from https://www.programming-idioms.org/idiom/158/random-sublist/2123/haskell
randomSample :: Int -> [a] -> IO [a]
randomSample 0 _ = pure []
randomSample k x | k >= length x = pure x
randomSample k x = do
   i <- randomRIO (0, length x - 1)
   let (a, e:b) = splitAt i x
   l <- randomSample (k-1) (a ++ b)
   pure (e : l)

---------------------------
-- Relational "Programs" --
---------------------------

data ProgramRelation t = ProgramRelation { rp_aprogs :: [SpecImpProgram t]
                                         , rp_eprogs :: [SpecImpProgram t]
                                         } deriving Show

instance CollectableNames (ProgramRelation t) where
  namesIn (ProgramRelation aprogs eprogs) = Set.union (namesIn aprogs) (namesIn eprogs)
