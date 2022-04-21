module Orhle.InvGen.SearchQueue
  ( Entry(..)
  , Queue(..)
  , ScoreFunction
  , qEmpty
  , qInsert
  , qPop
  , qSize
  , sfBalanced
  , sfBreadthFirst
  , sfDepthFirst
  ) where

import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.IntSet as IntSet
import Data.Set ( Set )
import qualified Data.Set as Set
import Orhle.InvGen.Feature
import Orhle.InvGen.State
import Prettyprinter


-------------
-- Entries --
-------------

data Entry t = Entry
  { entryCandidate        :: FeatureIdSet
  , entryRejectedBads     :: BadStateIdSet
  , entryAcceptedConGoods :: ConcreteGoodStateIdSet
  , entryAcceptedAbsGoods :: AbstractGoodStateIdSet
  } deriving (Ord, Show)

instance Ord t => Eq (Entry t) where
  entry1 == entry2 = entryCandidate entry1 == entryCandidate entry2

instance Pretty t => Pretty (Entry t) where
  pretty (Entry candidate rejected acceptedCon acceptedAbs) = align $
        pretty "Candidate["
    <>  pretty (IntSet.size acceptedCon + IntSet.size acceptedAbs)
    <>  pretty "/"
    <>  pretty (IntSet.size rejected)
    <>  pretty "]:"
    <+> pretty (IntSet.toList candidate)


------------
-- Queues --
------------

data Queue t = Queue
  { qQueue    :: Map Int (Set (Entry t))
  , qScoreFun :: ScoreFunction t
  }

qEmpty :: ScoreFunction t -> Queue t
qEmpty = Queue Map.empty

qSize :: Queue t -> Int
qSize (Queue queue _) = Map.foldr (\set count -> count + Set.size set) 0 queue

qInsert :: Ord t => Entry t -> Queue t -> Queue t
qInsert entry (Queue queue scoreFun) =
  let score = scoreFun entry
  in case Map.lookup score queue of
    Nothing  -> Queue (Map.insert score (Set.singleton entry) queue) scoreFun
    Just set -> Queue (Map.insert score (Set.insert entry set) queue) scoreFun

qPop :: Ord t => Queue t -> (Maybe (Entry t), Queue t)
qPop q@(Queue queue scoreFun) =
  let mMaxView = Map.maxViewWithKey queue
  in case mMaxView of
    Nothing -> if (qSize q) /= 0
               then error "qPop: empty max view when size /= 0"
               else (Nothing, Queue queue scoreFun)
    Just ((key, maxSet), queue') ->
      let mMaxElt = Set.maxView maxSet
      in case mMaxElt of
        Nothing -> qPop (Queue (Map.delete key queue) scoreFun)
        Just (elt, maxSet') ->
          if Set.null maxSet'
          then (Just elt, Queue queue' scoreFun)
          else (Just elt, Queue (Map.insert key maxSet' queue') scoreFun)

---------------------
-- Score Functions --
---------------------

type ScoreFunction t = Entry t -> Int

sfBalanced :: ScoreFunction t
sfBalanced (Entry candidate rejectedBads acceptedConGoods acceptedAbsGoods) =
  let
    numRejected   = IntSet.size rejectedBads
    candidateSize = IntSet.size candidate
    acceptedSize  = IntSet.size acceptedConGoods + IntSet.size acceptedAbsGoods
  in (acceptedSize * numRejected) `div` candidateSize

sfBreadthFirst :: ScoreFunction t
sfBreadthFirst (Entry candidate _ _ _) =
  let candidateSize = IntSet.size candidate
  in -candidateSize

sfDepthFirst :: ScoreFunction t
sfDepthFirst (Entry candidate _ _ _) =
  let candidateSize = IntSet.size candidate
  in candidateSize
