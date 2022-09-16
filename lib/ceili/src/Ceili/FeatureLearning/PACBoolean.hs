module Ceili.FeatureLearning.PACBoolean
  ( Clause
  , ClauseOccur(..)
  , FeatureVector
  , clauseToAssertion
  , clausesToAssertion
  , clausesWithSize
  , greedySetCover
  , learnBoolExpr
  , removeInconsistentClauses
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector
import Prettyprinter


type FeatureVector = Vector Bool

-- |Looks for a Boolean combination (in CNF) of the given assertions which
-- separates the given positive ("good") and negative ("bad") feature vectors.
-- Each feature vector in the good / bad collection is assumed to have the same
-- size as the assertion vector, with each feature vector index corresponding to
-- the valuation of the assertion vector at that index.
--
-- For example, if the assertions vector is [X, Y, Z] and the "good" feature
-- vectors are [ [T, F, F], [F, F, T], [F, T, T] ], then X is True in good
-- feature vector 0 and False in good feature vectors 1 and 2. The Boolean
-- combination X \/ Z would be a candidate solution, as it accepts all three
-- good vectors. Whether or not this is a real solution depends on whether or
-- not it also rejects all "bad" feature vectors.
--
-- This algorithm favors smaller Boolean combinations by searching smaller
-- formula sizes before moving on to larger ones. If no possible combination of
-- the given assertions separates the positive and negative samples, the
-- algorithm will not terminate.
learnBoolExpr :: Pretty t
              => Vector (Assertion t)
              -> Vector FeatureVector
              -> Vector FeatureVector
              -> Ceili (Assertion t)
learnBoolExpr features negFV posFV = do
  log_d "[PAC] Begin learning boolean expression..."
  boolLearn features negFV posFV 1 Vector.empty

boolLearn :: Pretty t
          => Vector (Assertion t)
          -> Vector FeatureVector
          -> Vector FeatureVector
          -> Int
          -> Vector Clause
          -> Ceili (Assertion t)
boolLearn features negFV posFV k prevClauses = do
  log_d $ "[PAC] Looking at clauses of size " ++ show k
  let nextClauses    = clausesWithSize k $ Vector.length features
  let consistentNext = removeInconsistentClauses nextClauses posFV
  let clauses        = consistentNext Vector.++ prevClauses
  let mSolution      = greedySetCover clauses negFV
  case mSolution of
    Just solution -> do
      let assertion = clausesToAssertion features $ Vector.toList solution
      log_d $ "[PAC] Learned boolean expression: " ++ (show . pretty) assertion
      return $ assertion
    Nothing -> boolLearn features negFV posFV (k + 1) clauses

-- |Removes all clauses which falsify at least one feature vector in the given vector of FVs.
removeInconsistentClauses :: Vector Clause -> Vector FeatureVector -> Vector Clause
removeInconsistentClauses clauses fvs = Vector.filter consistent clauses
  where
    falsifiesAny clause = or $ Vector.map (\fv -> falsifies fv clause) fvs
    consistent = not . falsifiesAny

-- |Attempts to find the smallest subset of clauses such that each of the given
-- feature vectors are falsified by at least one clause in the subset.
greedySetCover :: Vector Clause -> Vector FeatureVector -> Maybe (Vector Clause)
greedySetCover clauses fvs =
  case Vector.length clauses of
    0 -> if Vector.length fvs == 0 then (Just clauses) else Nothing
    _ ->
      let
        -- Find the clause that eliminates the most feature vectors.
        step curIdx curClause bestSoFar@(bestCount, _, _, _) = let
          -- curFV: the FVs that are left after the curClause falsifies all it can.
          -- curCount: how many FVs were falsified by the curClause.
          curFv    = Vector.filter (\fv -> not $ falsifies fv curClause) fvs
          curCount = (Vector.length fvs) - (Vector.length curFv)
          in if curCount > bestCount
             then (curCount, curIdx, curClause, curFv)
             else bestSoFar
        (elimCount, idx, clause, fv') = Vector.ifoldr step (-1, -1, Map.empty, Vector.empty) clauses
      in
        -- If we didn't eliminate any feature vectors, fail.
        if elimCount < 1 then Nothing
        -- If the best clause eliminates all FVs, return. Otherwise, recurse.
        else case length fv' of
               0 -> Just $ Vector.singleton clause
               _ -> do
                 let clauses' = Vector.ifilter (\i _ -> i /= idx) clauses
                 rest <- greedySetCover clauses' fv'
                 return $ clause `Vector.cons` rest


----------------------------------
-- Sparse Clause Representation --
----------------------------------

{-|
  Each Clause represents a disjunction of assertions from some vector V of
  possible assertions. The disjunctions are stored as a sparse mapping (assertions
  not present in the disjunction do not appear in the mapping) from an index in V
  to either CPos or CNeg, indicating whether the assertion appears positively or
  negatively, respectively.

  For example, given assertions [ x = 0, x < y, y < 5 ], the formula:
     x = 0 \/ y < 5
  would be represented:
    [0 -> CPos, 2 -> CPos]

  and the formula:
    x >= y \/ y < 5
  would be represented:
    [1 -> CNeg, 2 -> CPos]
-}
type Clause = Map Int ClauseOccur
data ClauseOccur = CPos | CNeg
  deriving (Show, Ord, Eq)

-- |Convert a Clause to an Assertion using its backing vector of available assertions.
clauseToAssertion :: Vector (Assertion t) -> Clause -> (Assertion t)
clauseToAssertion assertions clause = let
  toAssertion (idx, occur) = case occur of
    CPos -> assertions!idx
    CNeg -> Not $ assertions!idx
  in case map toAssertion $ Map.toList clause of
       []     -> ATrue
       (a:[]) -> a
       as     -> Or as

-- |Convert a list of Clause to an Assertion using a backing assertion vector.
clausesToAssertion :: Vector (Assertion t) -> [Clause] -> (Assertion t)
clausesToAssertion assertions clauses =
  case map (clauseToAssertion assertions) clauses of
    []     -> ATrue
    (a:[]) -> a
    as     -> And as

-- |A Clause falsifies a feature vector when every disjunct in the clause
-- disagrees with the feature vector.
falsifies :: FeatureVector -> Clause -> Bool
falsifies fv clause = and $ map conflicts $ Map.toList clause
  where
    conflicts (i, occur) = case occur of
      CPos -> not $ fv!i
      CNeg -> fv!i

-- |Enumerate all possible clauses of a given size or smaller.
clausesWithSize :: Int -> Int -> Vector Clause
clausesWithSize size numFeatures =
  if numFeatures < 1 then Vector.empty
  else if size > numFeatures then Vector.empty
  else case size of
    0 -> Vector.empty
    1 -> let
      neg = Vector.fromList $ map (\i -> Map.singleton i CNeg) [0..numFeatures-1]
      pos = Vector.fromList $ map (\i -> Map.singleton i CPos) [0..numFeatures-1]
      in neg Vector.++ pos
    _ -> let
      prev    = clausesWithSize (size - 1) (numFeatures - 1)
      neg     = Vector.map (\clause -> Map.insert (numFeatures - 1) CNeg clause) prev
      pos     = Vector.map (\clause -> Map.insert (numFeatures - 1) CPos clause) prev
      smaller = clausesWithSize size $ numFeatures - 1
      in neg Vector.++ pos Vector.++ smaller
