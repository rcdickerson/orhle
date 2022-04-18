module Orhle.InvGen.Clause
  ( Clause(..)
  , addClauseRemovingCovered
  , clausesAcceptedConGoods
  , clausesAcceptedAbsGoods
  , clausesRejectedBads
  , clauseToAssertion
  , clausesToAssertion
  ) where

import Ceili.Assertion
import qualified Data.IntSet as IntSet
import Orhle.InvGen.Feature
import Orhle.InvGen.State
import Prettyprinter

data Clause t = Clause
  { clauseFeatures         :: FeatureIdSet
  , clauseAcceptedConGoods :: ConcreteGoodStateIdSet
  , clauseAcceptedAbsGoods :: AbstractGoodStateIdSet
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Clause t) where
  pretty (Clause features _ _) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Features:" <+> pretty (IntSet.toList features)
    ]

clauseToAssertion :: FeatureCache t -> Clause t -> Assertion t
clauseToAssertion fc =
  aAnd . map featAssertion . fcLookupFeatures fc . IntSet.toList . clauseFeatures

clausesToAssertion :: FeatureCache t -> [Clause t] -> Assertion t
clausesToAssertion fc = aOr . map (clauseToAssertion fc)

clausesAcceptedConGoods :: [Clause t] -> ConcreteGoodStateIdSet
clausesAcceptedConGoods = IntSet.unions . map clauseAcceptedConGoods

clausesAcceptedAbsGoods :: [Clause t] -> ConcreteGoodStateIdSet
clausesAcceptedAbsGoods = IntSet.unions . map clauseAcceptedAbsGoods

clausesRejectedBads :: Ord t => FeatureCache t -> [Clause t] -> BadStateIdSet
clausesRejectedBads fc = IntSet.unions
                       . map (\fid -> fcRejectedBads fid fc)
                       . IntSet.toList
                       . IntSet.unions
                       . map clauseFeatures

addClauseRemovingCovered :: [Clause t] -> Clause t -> [Clause t]
addClauseRemovingCovered clauses newClause =
  let
    clause1 `covers` clause2 =
      (clauseAcceptedConGoods clause2 `IntSet.isSubsetOf` clauseAcceptedConGoods clause1) &&
      (clauseAcceptedAbsGoods clause2 `IntSet.isSubsetOf` clauseAcceptedAbsGoods clause1)
  in newClause:(filter (\c -> not $ newClause `covers` c) clauses)
