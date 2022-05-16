module Orhle.ChoiceStratGen
  (
  ) where

import Ceili.CeiliEnv
import Ceili.Assertion
import Ceili.ProgState
import Data.Set ( Set )
import Orhle.ChoiceState
import qualified Orhle.InvGen.OrhleInvGenConc as OIG

-- data Job t = Job
--   { jobChoiceVars       :: [Name]
--   , jobBadStates        :: [ProgState Integer]
--   , jobGoodStates       :: [ChoiceState t]
--   , jobLoopConds        :: [Assertion Integer]
--   , jobPost             :: Assertion Integer
--   , jobFeatureGenerator :: Int -> Set (Assertion Integer)
--   , jobWpTransform      :: Assertion Integer -> Ceili (Assertion Integer)
--   }

-- choiceStratGen :: Job t -> Ceili (Maybe ([ChoiceStrategy t Integer], Assertion Integer))
-- choiceStratGen job = do
--   let strats = possibleStrategies $ jobChoiceVars job
--   firstThatWorks strats job

-- firstThatWorks :: [[ChoiceStrategy t Integer]]
--                -> Job t
--                -> Ceili (Maybe ([ChoiceStrategy t Integer], Assertion Integer))
-- firstThatWorks [] _ = pure Nothing
-- firstThatWorks (strats:rest) job = do
--   result <- tryStrategies strats job
--   case result of
--     Nothing    -> firstThatWorks rest job
--     Just invar -> pure $ Just (strats, invar)

-- possibleStrategies :: [Name] -> [[ChoiceStrategy t Integer]]
-- possibleStrategies [] = []
-- possibleStrategies (name:[]) = [[ChoiceStrategy name (\a -> error "")]]
-- possibleStrategies _ = error "Multiple choice variables unsupported"

-- tryStrategies :: [ChoiceStrategy t Integer]
--               -> Job t
--               -> Ceili (Maybe (Assertion Integer))
-- tryStrategies strats job = do
--   let goodStates = map (reifyChoices strats) (jobGoodStates job)
--   let badStates  = jobBadStates job
--   let oigConfig = OIG.Configuration { OIG.cfgMaxFeatureSize   = 2
--                                     , OIG.cfgMaxClauseSize    = 12
--                                     , OIG.cfgFeatureGenerator = jobFeatureGenerator job
--                                     , OIG.cfgWpTransform      = jobWpTransform job
--                                     }
--   let oigJob = OIG.Job { OIG.jobBadStates  = badStates
--                        , OIG.jobGoodStates = goodStates
--                        , OIG.jobLoopConds  = jobLoopConds job
--                        , OIG.jobPost       = jobPost job
--                        }
--   OIG.orhleInvGen oigConfig oigJob
