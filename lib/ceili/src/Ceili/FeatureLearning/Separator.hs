{-# LANGUAGE FlexibleContexts #-}

module Ceili.FeatureLearning.Separator
  ( findSeparator
  ) where

import Ceili.CeiliEnv
import Ceili.ProgState
import Ceili.StatePredicate
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter


findSeparator :: (Pretty p, Pretty s, StatePredicate p s) =>
                 Int
              -> (Int -> Set p)
              -> [ProgState s]
              -> [ProgState s]
              -> Ceili (Maybe p)
findSeparator maxCandidateSize candidatesOfSize goodTests badTests = let
  featureLearn' size = do
    log_d $ "[Separator] Examining candidate separators of size " ++ show size
    let candidates = Set.toList $ candidatesOfSize size
    mFeature <- firstThatSeparates goodTests badTests candidates
    case mFeature of
      Nothing ->
        if size >= maxCandidateSize
        then logMaxSizeReached maxCandidateSize >> return Nothing
        else featureLearn' (size + 1)
      Just feature -> do
        log_d $ "[Separator] Found separator: " ++ (show . pretty) feature
        return $ Just feature
  in do
    log_d   "[Separator] Beginning separator search"
    log_d . show $ pretty "[Separator] Good tests: " <+> (align . prettyProgStates $ goodTests)
    log_d . show $ pretty "[Separator] Bad tests: " <+> (align . prettyProgStates $ badTests)
    featureLearn' 1

firstThatSeparates :: StatePredicate p s
                   => [ProgState s]
                   -> [ProgState s]
                   -> [p]
                   -> Ceili (Maybe p)
firstThatSeparates goodTests badTests assertions =
  case assertions of
    []   -> return Nothing
    a:as -> do
      accepts <- acceptsAll goodTests a
      rejects <- rejectsAll badTests a
      if accepts && rejects
        then return $ Just a
        else firstThatSeparates goodTests badTests as

acceptsAll :: StatePredicate p s => [ProgState s] -> p -> Ceili Bool
acceptsAll states assertion =
  return . and . map (treatErrorsAs False) =<< mapM (\state -> testState assertion state) states

rejectsAll :: StatePredicate p s => [ProgState s] -> p -> Ceili Bool
rejectsAll states assertion =
  return . and . map not . map (treatErrorsAs True) =<< mapM (\state -> testState assertion state) states

treatErrorsAs :: Bool -> PredicateResult -> Bool
treatErrorsAs err result = case result of
  Accepted -> True
  Rejected -> False
  Error _  -> err

logMaxSizeReached :: Int -> Ceili ()
logMaxSizeReached maxSize = log_d $
  "[Separator] Could not find separator within size bound (" ++ show maxSize ++ ")"
