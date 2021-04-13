module Orhle.LinearInequalities
  ( linearInequalities
  ) where

import           Data.Maybe ( fromJust, isJust )
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion )
import qualified Orhle.Assertion as A
import           Orhle.Name ( TypedName, namesIn )

-- Enumerate all inequalities of the form i + j*x + k*y + ... <= v,
-- where the left hand side has `size` terms, (i, j, k, ...) are drawn
-- from `nums` + {-1, 0, 1}, (x, y, ...) are drawn from `varNames`,
-- and v is drawn from `nums` union `varNames`. The same `nums` may
-- appear multiple places in the inequality, but each `varName` will
-- appear at most once.
linearInequalities :: Int -> Set Integer -> Set TypedName -> Set Assertion
linearInequalities size nums varNames =
  if (Set.size varNames < size) then error $ "Need at least " ++ (show $ size) ++ " vars"
  else let
  numAriths   = Set.map A.Num $ Set.insert 0 $ Set.insert 1 $ Set.insert (-1) nums
  varAriths   = Set.map A.Var varNames
  varGroups   = subsets size varAriths
  coeffGroups = chooseWithReplacement size numAriths
  combos      = catMaybes $ Set.map (uncurry constructLC) $
                Set.cartesianProduct coeffGroups varGroups
  bounds      = Set.union numAriths varAriths
  ineqPairs   = Set.filter (uncurry namesDisjoint) $
                Set.filter (uncurry atLeastOneVar) $
                Set.cartesianProduct bounds combos
  in Set.unions [ Set.map (uncurry A.Lte) ineqPairs
                , Set.map (uncurry A.Gte) ineqPairs
                ]

constructLC :: [A.Arith] -> [A.Arith] -> Maybe A.Arith
constructLC coeffs vars = let
  terms = removeZeros $ map (\(c,v) -> A.Mul [c, v]) $ zip coeffs vars
  in case terms of
       [] -> Nothing
       _  -> Just $ A.Add terms

namesDisjoint :: A.Arith -> A.Arith -> Bool
namesDisjoint a b = Set.null $ Set.intersection (namesIn a) (namesIn b)

atLeastOneVar :: A.Arith -> A.Arith -> Bool
atLeastOneVar a b = not . Set.null $ Set.union (namesIn a) (namesIn b)

catMaybes :: Ord a => Set (Maybe a) -> Set a
catMaybes set = Set.map fromJust $ Set.filter isJust set

removeZeros :: [A.Arith] -> [A.Arith]
removeZeros as = case as of
  [] -> []
  (a:as') -> case a of
               A.Num 0  -> removeZeros as'
               A.Mul ms -> if any (== A.Num 0) ms
                           then removeZeros as'
                           else a:(removeZeros as')
               _        -> a:(removeZeros as')

subsets :: Ord a => Int -> Set a -> Set [a]
subsets 0 _ = Set.singleton []
subsets size as = if Set.null as then Set.empty else
  let
    (a, as') = Set.deleteFindMin as
    asubs    = Set.map (a:) $ subsets (size - 1) as'
    others   = subsets size as'
  in Set.union asubs others

chooseWithReplacement :: Ord a => Int -> Set a -> Set [a]
chooseWithReplacement 0 _ = Set.singleton []
chooseWithReplacement n as =
  let prev = chooseWithReplacement (n - 1) as
  in  Set.map (uncurry (:)) $ Set.cartesianProduct as prev

chooseNoReplacement :: Ord a => Int -> Set a -> Set [a]
chooseNoReplacement 0 _ = Set.singleton []
chooseNoReplacement n as =
  if (Set.size as < n) then error $ "Need at least " ++ show n ++ " items"
  else let f a = chooseNoReplacement (n - 1) $ Set.delete a as
       in Set.unions $ Set.map (\a -> Set.map (a:) (f a)) as
