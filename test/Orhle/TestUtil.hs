{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.TestUtil
  ( assertEquivalent
  , assertionFromStr
  , assertSameElements
  , evalCeili
  ) where

import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import qualified Ceili.SMT as SMT
import Ceili.SMTString
import Data.Set ( Set )
import qualified Data.Set as Set


assertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                 => Assertion t -> Assertion t -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  solver <- mkSolver
  result <- runCeili (defaultEnv solver Set.empty) $ checkValidWithLog LogLevelNone iff
  case result of
    Left err               -> assertFailure $ show err
    Right SMT.Valid        -> return () -- pass
    Right (SMT.Invalid s)  -> assertFailure $ unlines ["Not equivalent: ", showSMT a1, "and", showSMT a2, "model:", s]
    Right SMT.ValidUnknown -> assertFailure "Unable to establish equivalence, solver returned UNK."

assertSameElements :: (Ord t, Show t) => [t] -> [t] -> IO ()
assertSameElements list1 list2 = assertEqual (Set.fromList list1) (Set.fromList list2)

assertionFromStr :: AssertionParseable t => String -> IO (Assertion t)
assertionFromStr str =
  let assertion = parseAssertion str
  in case assertion of
    Left err -> assertFailure (show err)
    Right a  -> pure a

evalCeili :: Set Name -> Ceili a -> IO a
evalCeili names task = do
  solver <- mkSolver
  let env = mkEnv solver LogLevelDebug 2000 names
  mResult <- runCeili env task
  case mResult of
    Left err     -> assertFailure $ show err
    Right result -> pure result
