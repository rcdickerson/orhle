module Orhle.InvGen.ClauseConc
  ( Clause(..)
  , addClauseRemovingCovered
  , clausesAcceptedGoods
  , clauseToAssertion
  , clausesToAssertion
  ) where

import Ceili.Assertion
import qualified Data.IntSet as IntSet
import Orhle.InvGen.FeatureConc
import Orhle.InvGen.StateConc
import Prettyprinter

data Clause t = Clause
  { clauseFeatures      :: FeatureIdSet
  , clauseAcceptedGoods :: GoodStateIdSet
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Clause t) where
  pretty (Clause features _) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Features:" <+> pretty (IntSet.toList features)
    ]

clauseToAssertion :: FeatureCache t -> Clause t -> Assertion t
clauseToAssertion fc =
  aAnd . map featAssertion . fcLookupFeatures fc . IntSet.toList . clauseFeatures

clausesToAssertion :: FeatureCache t -> [Clause t] -> Assertion t
clausesToAssertion fc = aOr . map (clauseToAssertion fc)

clausesAcceptedGoods :: [Clause t] -> GoodStateIdSet
clausesAcceptedGoods = IntSet.unions . map clauseAcceptedGoods

addClauseRemovingCovered :: [Clause t] -> Clause t -> [Clause t]
addClauseRemovingCovered clauses newClause =
  let
    clause1 `covers` clause2 =
      (clauseAcceptedGoods clause2 `IntSet.isSubsetOf` clauseAcceptedGoods clause1)
  in newClause:(filter (\c -> not $ newClause `covers` c) clauses)
