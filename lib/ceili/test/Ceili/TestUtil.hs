{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Ceili.TestUtil
  ( EmptyPieContextProvider(..)
  , assertEquivalent
  , assertHasSameItems
  , assertImplies
  , assertValid
  , envFunImp
  , envImp
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.FunImp
import Ceili.Language.Imp
import Ceili.Name
import qualified Ceili.SMT as SMT
import Ceili.SMTString
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import System.Log.FastLogger
import Test.Framework

data EmptyPieContextProvider = EmptyPieContextProvider
instance ImpPieContextProvider EmptyPieContextProvider Integer where
  impPieCtx _ = ImpPieContext Map.empty Set.empty Set.empty

envImp :: ImpProgram t -> Env
envImp prog = defaultEnv (namesIn prog)

envFunImp :: FunImpProgram t -> Env
envFunImp prog = defaultEnv (namesIn prog)

assertValid :: ValidCheckable t => Assertion t -> IO ()
assertValid assertion = do
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger assertion
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure $ "Invalid: " ++ s
    SMT.ValidUnknown -> assertFailure "Unable to validate, solver returned UNK."

assertImplies :: (SMTString t, SMTTypeString t, ValidCheckable t)
              => Assertion t -> Assertion t -> IO ()
assertImplies a1 a2 = do
  let imp = Imp a1 a2
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger imp
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure $ unlines ["Invalid implication: ", showSMT a1, "=>", showSMT a2, "model:", s]
    SMT.ValidUnknown -> assertFailure "Unable to establish implication, solver returned UNK."

assertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                 => Assertion t -> Assertion t -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger iff
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure $ unlines ["Not equivalent: ", showSMT a1, "and", showSMT a2, "model:", s]
    SMT.ValidUnknown -> assertFailure "Unable to establish equivalence, solver returned UNK."

assertHasSameItems :: (Ord a, Show a) => Vector a -> Vector a -> IO ()
assertHasSameItems expectedVec actualVec = let
  addToCount item counts = let current = Map.findWithDefault 0 item counts
                           in Map.insert item (current + 1) counts
  countItems = Vector.foldr addToCount Map.empty
  in assertEqual (countItems expectedVec) (countItems actualVec)
