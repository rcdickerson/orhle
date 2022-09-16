{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Ceili.StatePredicate
  ( PredicateResult(..)
  , StatePredicate(..)
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Evaluation
import Ceili.ProgState

data PredicateResult = Accepted
                     | Rejected
                     | Error String
                     deriving (Eq, Ord, Show)

class StatePredicate a s where
  testState :: a -> ProgState s -> Ceili PredicateResult

instance (ArithAlgebra t, AssertionAlgebra t) => Evaluable c t (Assertion t) PredicateResult
  where eval ctx state assertion =
          case eval ctx state assertion of
            True  -> Accepted
            False -> Rejected

instance StatePredicate (Assertion Integer) Integer where
  testState assertion state = return $ eval () state assertion
