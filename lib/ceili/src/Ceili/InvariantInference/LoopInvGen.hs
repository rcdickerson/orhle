{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- An implementation of LoopInvGen (with the core PIE
-- component abstracted, see the Ceili.FeatureLearning.Pie module)
-- from "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.InvariantInference.LoopInvGen
  ( SeparatorLearner(..)
  , loopInvGen
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.PTS ( BackwardPT )
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import qualified Data.Map as Map
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import Prettyprinter


----------------
-- Separators --
----------------

data SeparatorLearner ctx t = SeparatorLearner { sl_context :: ctx
                                               , sl_learnSeparator :: ctx
                                                                   -> [ProgState t]
                                                                   -> [ProgState t]
                                                                   -> Ceili (ctx, Maybe (Assertion t))
                                               , sl_resetSearch :: ctx -> Ceili ctx
                                             }


-----------------
-- Computation --
-----------------

data LigEnv c t = LigEnv { pe_goodTests        :: [ProgState t]
                         , pe_loopConds        :: [Assertion t]
                         , pe_goal             :: Assertion t
                         , pe_separatorLearner :: SeparatorLearner c t
                         }

type LigM c t a = StateT (LigEnv c t) Ceili a

envGoodTests :: LigM c t [ProgState t]
envGoodTests = return . pe_goodTests =<< get

envLoopConds :: LigM c t [Assertion t]
envLoopConds = return . pe_loopConds =<< get

envGoal :: LigM c t (Assertion t)
envGoal = return . pe_goal =<< get

learnSeparator :: [ProgState t] -> [ProgState t] -> LigM c t (Maybe (Assertion t))
learnSeparator badTests goodTests = do
  LigEnv goodStates loopConds goal (SeparatorLearner context learner resetf) <- get
  (context', result) <- lift $ learner context badTests goodTests
  put $ LigEnv goodStates loopConds goal (SeparatorLearner context' learner resetf)
  pure result

resetLearnerSearch :: LigM c t ()
resetLearnerSearch = do
  LigEnv goodStates loopConds goal (SeparatorLearner context learner resetf) <- get
  context' <- lift $ resetf context
  put $ LigEnv goodStates loopConds goal (SeparatorLearner context' learner resetf)

plog_e :: String -> LigM c t ()
plog_e = lift . log_e

plog_i :: String -> LigM c t ()
plog_i = lift . log_i

plog_d :: String -> LigM c t ()
plog_d = lift . log_d


----------------
-- LoopInvGen --
----------------

loopInvGen :: ( Embeddable Integer t
              , Ord t
              , Pretty t
              , SMT.ValidCheckable t
              , StatePredicate (Assertion t) t
              , AssertionParseable t )
           => c
           -> BackwardPT c p t
           -> [Assertion t]
           -> p
           -> Assertion t
           -> [ProgState t]
           -> SeparatorLearner lctx t
           -> Ceili (Maybe (Assertion t))
loopInvGen ctx backwardPT loopConds body post goodTests separatorLearner = do
  log_i $ "[LoopInvGen] Beginning invariant inference"
  let task = loopInvGen' ctx backwardPT body
  evalStateT task $ LigEnv goodTests loopConds post separatorLearner

loopInvGen' :: ( Embeddable Integer t
               , Ord t
               , Pretty t
               , SMT.ValidCheckable t
               , StatePredicate (Assertion t) t
               , AssertionParseable t )
            => c
            -> BackwardPT c p t
            -> p
            -> LigM lctx t (Maybe (Assertion t))
loopInvGen' ctx backwardPT body = do
  goodTests <- envGoodTests
  conds     <- envLoopConds
  goal      <- envGoal
  plog_i $ "[LoopInvGen] Searching for initial candidate invariant..."
  let nconds = aAnd $ map Not conds
  mInvar <- vPreGen (aImp nconds goal)
                    Vector.empty
                    (Vector.fromList goodTests)
  case mInvar of
    Nothing -> do
      plog_i "[LoopInvGen] Unable to find initial candidate invariant (an I s.t. I /\\ ~c => Post)"
      return Nothing
    Just invar -> do
      lift . log_i $ "[LoopInvGen] Initial invariant: " ++ (show . pretty) mInvar
      mInvar' <- resetLearnerSearch >> makeInductive backwardPT ctx body invar
      case mInvar' of
         Nothing -> do
           plog_i "[LoopInvGen] Unable to find inductive strengthening"
           return Nothing -- TODO: Not this.
         Just invar' -> do
           plog_i $ "[LoopInvGen] Strengthened (inductive) invariant: " ++ (show . pretty) mInvar'
           plog_i $ "[LoopInvGen] Attempting to weaken invariant..."
           let validInvar inv = lift $ do
                 wp <- backwardPT ctx body inv
                 checkValidB $ And [ Imp (And [nconds, inv]) goal
                                   , Imp (And $ inv:conds) wp ]
           weakenedInvar <- weaken validInvar invar'
           plog_i $ "[LoopInvGen] Inference complete. Learned invariant: " ++ (show . pretty) weakenedInvar
           return $ Just weakenedInvar

makeInductive :: ( Embeddable Integer t
                 , Ord t
                 , Pretty t
                 , SMT.ValidCheckable t
                 , StatePredicate (Assertion t) t
                 , AssertionParseable t )
              => BackwardPT c p t
              -> c
              -> p
              -> Assertion t
              -> LigM lctx t (Maybe (Assertion t))
makeInductive backwardPT ctx body invar = do
  plog_d $ "[LoopInvGen] Checking inductivity of candidate invariant: " ++ (show . pretty) invar
  conds <- envLoopConds
  goodTests <- envGoodTests
  wp <- lift $ backwardPT ctx body invar
  let query = Imp (And $ invar:conds) wp
  response <- lift $ checkValid query
  mInvar <- case response of
    SMT.Valid        -> return $ Just invar
    SMT.Invalid _    -> return Nothing
    SMT.ValidTimeout -> do
      plog_e $ "[LoopInvGen] SMT timed out when checking inductivity. "
               ++ "Treating candidate as non-inductive. SMT query: "
               ++ show query
      return Nothing
    SMT.ValidUnknown -> do
      plog_e $ "[LoopInvGen] SMT solver returned unknown when checking inductivity. "
               ++ "Treating candidate as non-inductive. SMT query: "
               ++ show query
      return Nothing
  case mInvar of
    Just _  -> do
      plog_i $ "[LoopInvGen] Candidate invariant is inductive"
      return mInvar
    Nothing -> do
      plog_i $ "[LoopInvGen] Candidate invariant not inductive, attempting to strengthen"
      inductiveWP <- lift $ backwardPT ctx body invar
      let goal = Imp (And $ invar:conds) inductiveWP
      mInvar' <- vPreGen goal Vector.empty (Vector.fromList goodTests)
      case mInvar' of
        Nothing -> do
          plog_d $ "[LoopInvGen] Unable to find inductive strengthening of " ++ show invar
          return Nothing
        Just invar' -> do
          plog_d $ "[LoopInvGen] Found strengthening candidate clause: " ++ show invar'
          makeInductive backwardPT ctx body (conj invar invar')

-- |A conjoin that avoids extraneous "and" nesting.
conj :: Assertion t -> Assertion t -> Assertion t
conj a1 a2 =
  case (a1, a2) of
    (And as, _) -> And (a2:as)
    (_, And as) -> And (a1:as)
    _           -> And [a1, a2]

weaken :: (Assertion t -> LigM lctx t Bool) -> Assertion t -> LigM lctx t (Assertion t)
weaken sufficient assertion = do
  let aconjs = conjuncts assertion
  aconjs' <- paretoOptimize (sufficient . conjoin) aconjs
  return $ conjoin aconjs'

conjuncts :: Assertion t -> [Assertion t]
conjuncts assertion = case assertion of
  And as -> concat $ map conjuncts as
  _      -> [assertion]

conjoin :: [Assertion t] -> Assertion t
conjoin as = case as of
  []     -> ATrue
  (a:[]) -> a
  _      -> And as

paretoOptimize :: ([Assertion t] -> LigM lctx t Bool) -> [Assertion t] -> LigM lctx t [Assertion t]
paretoOptimize sufficient assertions =
  let
    optimize (needed, toExamine) =
      case toExamine of
        []     -> return $ needed
        (a:as) -> do
          worksWithoutA <- sufficient (needed ++ as)
          if worksWithoutA
            then optimize (needed, as)
            else optimize (a:needed, as)
  in optimize ([], assertions)


-------------
-- vPreGen --
-------------

vPreGen :: ( Embeddable Integer t
           , Ord t
           , Pretty t
           , SMT.ValidCheckable t
           , StatePredicate (Assertion t) t
           , AssertionParseable t )
        => (Assertion t)
        -> Vector (ProgState t)
        -> Vector (ProgState t)
        -> LigM lctx t (Maybe (Assertion t))
vPreGen goal badTests goodTests = do
  plog_d $ "[LoopInvGen] Starting vPreGen pass"
--  plog_d . show $ pretty "[LoopInvGen] goal: " <+> pretty goal
  plog_d . show $ pretty "[LoopInvGen] good tests: "  <+> pretty (length goodTests)
  plog_d . show $ pretty "[LoopInvGen] bad tests: "  <+> pretty (length badTests)
  mCandidate <- learnSeparator (Vector.toList badTests) (Vector.toList goodTests)
  case mCandidate of
    Nothing -> return Nothing
    Just candidate -> do
      plog_d $ "[LoopInvGen] vPreGen candidate precondition: " ++ (show . pretty) candidate
      mCounter <- lift . findCounterexample $ Imp candidate goal
      case mCounter of
        Counterexample counter -> do
          plog_d $ "[LoopInvGen] vPreGen found counterexample: " ++ show counter
          let badTests' = Vector.cons (extractState counter) badTests
          vPreGen goal badTests' goodTests
        FormulaValid -> do
          plog_d $ "[LoopInvGen] vPreGen found satisfactory precondition: " ++ show candidate
          return $ Just candidate
        SMTTimeout -> do
          throwError $ "[LoopInvGen] SMT timed out on candidate: " ++ show candidate
        SMTUnknown -> do
          throwError $ "[LoopInvGen] SMT returned unknown on candidate: " ++ show candidate

-- TODO: This is fragile.
extractState :: Pretty t => (Assertion t) -> (ProgState t)
extractState assertion = case assertion of
  Eq lhs rhs -> Map.fromList [(extractName lhs, extractInt rhs)]
  And as     -> Map.unions $ map extractState as
  _          -> error $ "Unexpected assertion: " ++ show assertion
  where
    extractName arith = case arith of
      Var name -> name
      _ -> error $ "Unexpected arith (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      _ -> error $ "Unexpected arith (expected int): " ++ show arith
