module Orhle.InvGen.Clause
  ( Clause(..)
  , clausesAcceptedConGoods
  , clausesOptimisticAcceptedAbsGoods
  , clausesRejectedBads
  , clauseToAssertion
  , clausesToAssertion
  ) where

import Ceili.Assertion
import Data.IntSet ( IntSet )
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
clausesAcceptedConGoods = intersections . map clauseAcceptedConGoods

clausesOptimisticAcceptedAbsGoods :: [Clause t] -> ConcreteGoodStateIdSet
clausesOptimisticAcceptedAbsGoods = intersections . map clauseAcceptedAbsGoods

clausesRejectedBads :: Ord t => FeatureCache t -> [Clause t] -> BadStateIdSet
clausesRejectedBads fc = IntSet.unions
                       . map (\fid -> fcRejectedBads fid fc)
                       . IntSet.toList
                       . IntSet.unions
                       . map clauseFeatures

intersections :: [IntSet] -> IntSet
intersections []     = IntSet.empty
intersections (s:ss) = foldr IntSet.intersection s ss
