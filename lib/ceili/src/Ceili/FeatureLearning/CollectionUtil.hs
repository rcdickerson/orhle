-- Some miscellaneous utility functions for dealing with
-- collections.

module Ceili.FeatureLearning.CollectionUtil
  ( chooseWithReplacement
  , setToVec
  , subsetsOfSize
  , vecToSet
  ) where

import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Vector ( Vector )
import qualified Data.Vector as Vector

-- Like powerSet, but restricted to subsets of the given size.
subsetsOfSize :: Ord a => Int -> Set a -> Set (Set a)
subsetsOfSize n as =
  if (n > Set.size as) then Set.empty
  else case n of
    0 -> Set.empty
    1 -> Set.map Set.singleton as
    _ -> let
      (a, as') = Set.deleteFindMin as
      asubs    = Set.map (Set.insert a) $ subsetsOfSize (n - 1) as'
      others   = subsetsOfSize n as'
      in Set.union asubs others

-- Choose a number of elemets from the given set with replacement
-- (i.e., the same element may appear in each choice list multiple
-- times).
chooseWithReplacement :: Ord a => Int -> Set a -> Set [a]
chooseWithReplacement n as =
  case n of
    0 -> Set.empty
    1 -> Set.map (:[]) as
    _ -> let prev = chooseWithReplacement (n - 1) as
         in  Set.map (uncurry (:)) $ Set.cartesianProduct as prev

-- Convenience conversion from Vector to Set.
vecToSet :: Ord a => Vector a -> Set a
vecToSet = Set.fromList . Vector.toList

-- Convenience conversion from Set to Vector.
setToVec :: Ord a => Set a -> Vector a
setToVec = Vector.fromList . Set.toList
