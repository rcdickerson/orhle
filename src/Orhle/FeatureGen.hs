{-# LANGUAGE FlexibleContexts #-}

module Orhle.FeatureGen
  ( Logic(..)
  , Operator(..)
  , genFeatures
  , lia
  ) where

import Ceili.Assertion
import Ceili.Embedding
import Ceili.Name
import Data.List ( sort )
import qualified Data.Set as Set

data Logic t = Logic
  { lName            :: String
  , lArithToBoolOps  :: [Operator (Arith t) (Assertion t)]
  , lArithToArithOps :: [Operator (Arith t) (Arith t)]
  , lFeatureFilters  :: [FeatureFilter t]
  , lTermFilters     :: [TermFilter t]
  }

data Operator i o = Operator
  { opName  :: String
  , opApp   :: [i] -> o
  }

type FeatureFilter t = Assertion t -> Bool
type TermFilter t = Arith t -> Bool

binop :: String -> (i -> i -> o) -> Operator i o
binop name app = Operator { opName  = name
                          , opApp   = appOrErr
                          }
  where
    appOrErr (a1:a2:[]) = app a1 a2
    appOrErr args       = error $ name ++ " has arity 2, given " ++ (show $ length args) ++ " args"

lia :: (Ord t, Embeddable Integer t) => Logic t
lia = Logic
  { lName = "LIA"
  , lArithToBoolOps  = [ binop "=" Eq
--                       , binop "<" Lt
--                       , binop ">" Gt
                       , binop "<=" Lte
--                       , binop ">=" Gte
                       ]
  , lArithToArithOps = [-- Operator "+" Add
                         Operator "-" Sub
                       , Operator "*" Mul
                       ]
  , lFeatureFilters  = [ eqRefl
                       , requireVars
                       , ignoreSymmetricAdds
                       , ignoreSymmetricSubs
                       , ignoreSymmetricMuls
                       , oneVarOccurencePerFeature
                       ]
  , lTermFilters     = [ linear
                       , ignoreAddZero
                       , ignoreSubZero
                       , ignoreMulZero
                       , ignoreMulOne
                       , ignoreOpsWithoutVars
                       , oneVarOccurencePerTerm
                       , addCommutative
                       , mulCommutative
                       ]
  }

filterFeatures :: Logic t -> [Assertion t] -> [Assertion t]
filterFeatures logic features =
  let meetsAll feat = all ($feat) (lFeatureFilters logic)
  in filter meetsAll features

filterTerms :: Logic t -> [Arith t] -> [Arith t]
filterTerms logic terms =
  let meetsAll term = all ($term) (lTermFilters logic)
  in filter meetsAll terms

eqRefl :: Ord t => FeatureFilter t
eqRefl feature =
  -- Use the ordering of t to ensure only one of (= a b) and (= b a) ever appears.
  case feature of
    (Eq a b) | a <= b -> False
    _ -> True

requireVars :: FeatureFilter t
requireVars feature =
  case feature of
    Eq  (Num _) (Num _) -> False
    Gt  (Num _) (Num _) -> False
    Lt  (Num _) (Num _) -> False
    Gte (Num _) (Num _) -> False
    Lte (Num _) (Num _) -> False
    _ -> True

ignoreSymmetricAdds :: Eq t => FeatureFilter t
ignoreSymmetricAdds feature =
  let containsSameNum as bs = any (`elem` bs) as
  in case feature of
    Eq  (Add as) (Add bs) | containsSameNum as bs -> False
    Gt  (Add as) (Add bs) | containsSameNum as bs -> False
    Lt  (Add as) (Add bs) | containsSameNum as bs -> False
    Gte (Add as) (Add bs) | containsSameNum as bs -> False
    Lte (Add as) (Add bs) | containsSameNum as bs -> False
    _ -> True

ignoreSymmetricSubs :: Eq t => FeatureFilter t
ignoreSymmetricSubs feature =
  let containsSameNum as bs = any (`elem` bs) as
  in case feature of
    Eq  (Sub as) (Sub bs) | containsSameNum as bs -> False
    Gt  (Sub as) (Sub bs) | containsSameNum as bs -> False
    Lt  (Sub as) (Sub bs) | containsSameNum as bs -> False
    Gte (Sub as) (Sub bs) | containsSameNum as bs -> False
    Lte (Sub as) (Sub bs) | containsSameNum as bs -> False
    _ -> True

ignoreSymmetricMuls :: Eq t => FeatureFilter t
ignoreSymmetricMuls feature =
  let containsSameNum as bs = any (`elem` bs) as
  in case feature of
    Eq  (Mul as) (Mul bs) | containsSameNum as bs -> False
    _ -> True

oneVarOccurencePerFeature :: Ord t => FeatureFilter t
oneVarOccurencePerFeature feature =
  let hasDuplicates rhs lhs =
        let namesList = Set.toList (namesIn lhs) ++ Set.toList (namesIn rhs)
        in Set.size (Set.fromList namesList) < length namesList
  in case feature of
    Eq  lhs rhs | hasDuplicates lhs rhs -> False
    Lt  lhs rhs | hasDuplicates lhs rhs -> False
    Gt  lhs rhs | hasDuplicates lhs rhs -> False
    Lte lhs rhs | hasDuplicates lhs rhs -> False
    Gte lhs rhs | hasDuplicates lhs rhs -> False
    _ -> True

ignoreMulZero :: (Eq t, Embeddable Integer t) => TermFilter t
ignoreMulZero term =
  let zero = Num $ embed (0 :: Integer)
  in case term of
    Mul as | any (== zero) as -> False
    _ -> True

ignoreMulOne :: (Eq t, Embeddable Integer t) => TermFilter t
ignoreMulOne term =
  let one = Num $ embed (1 :: Integer)
  in case term of
    Mul as | any (== one) as -> False
    _ -> True

ignoreAddZero :: (Eq t, Embeddable Integer t) => TermFilter t
ignoreAddZero term =
  let zero = Num $ embed (0 :: Integer)
  in case term of
    Add [a, b] | a == zero || b == zero -> False
    _ -> True

ignoreSubZero :: (Eq t, Embeddable Integer t) => TermFilter t
ignoreSubZero term =
  let zero = Num $ embed (0 :: Integer)
  in case term of
    Sub [_, b] | b == zero -> False
    _ -> True

ignoreOpsWithoutVars :: TermFilter t
ignoreOpsWithoutVars term =
  case term of
    Add ts | all isNum ts -> False
    Sub ts | all isNum ts -> False
    Mul ts | all isNum ts -> False
    _ -> True

oneVarOccurencePerTerm :: Ord t => TermFilter t
oneVarOccurencePerTerm term =
  let hasDuplicates lst = Set.size (Set.fromList lst) < length lst
  in case term of
    Add ts | hasDuplicates ts -> False
    Sub ts | hasDuplicates ts -> False
    Mul ts | hasDuplicates ts -> False
    _ -> True

addCommutative :: Ord t => TermFilter t
addCommutative term =
  case term of
    Add ts | ts /= sort ts -> False
    _ -> True

mulCommutative :: Ord t => TermFilter t
mulCommutative term =
  case term of
    Mul ts | ts /= sort ts -> False
    _ -> True

linear :: TermFilter t
linear term =
  case term of
    Mul ts -> length (filter (not . isNum) ts) <= 1
    _ -> True

isNum :: Arith t -> Bool
isNum a =
  case a of
    (Num _) -> True
    _ -> False

genFeatures :: Logic t -> [t] -> [Name] -> Int -> [Assertion t]
genFeatures logic literals names size =
  let (features, _) = genFeatures' logic literals names size
  in features

genFeatures' :: Logic t -> [t] -> [Name] -> Int -> ([Assertion t], [Arith t])
genFeatures' logic literals names 0 =
  let
    nums = map Num literals
    vars = map Var names
    terms = filterTerms logic $ nums ++ vars
  in ([], terms)
genFeatures' logic literals names size =
  let
    (features, terms) = genFeatures' logic literals names (size - 1)
    nextFeatures      = filterFeatures logic . concat . map (cartesianApply terms) $ lArithToBoolOps logic
    nextTerms         = filterTerms logic    . concat . map (cartesianApply terms) $ lArithToArithOps logic
  in (features ++ nextFeatures, terms ++ nextTerms)

cartesianApply :: [i] -> Operator i o -> [o]
cartesianApply terms op =
  let
    toList (lhs, rhs) = [lhs, rhs]
    inputs = map toList $ cartesianProduct terms terms
  in map (opApp op) inputs

cartesianProduct :: [a] -> [b] -> [(a, b)]
cartesianProduct xs ys = [(x,y) | x <- xs, y <- ys]
