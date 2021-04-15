module Orhle.PredTransTypes
  ( Loop(..)
  , LoopFusion(..)
  , RevLoop(..)
  , RevLoopFusion(..)
  ) where

import Orhle.Assertion ( Assertion(..) )
import Orhle.Imp
import Orhle.Triple

data Loop = Loop
  { l_body          :: Program
  , l_condAssertion :: Assertion
  , l_condBExp      :: BExp
  , l_holeId        :: Maybe Int
  , l_invar         :: Assertion
  } deriving Show

data RevLoop = RevLoop
  { rl_body          :: RevProgram
  , rl_condAssertion :: Assertion
  , rl_condBExp      :: BExp
  , rl_holeId        :: Maybe Int
  , rl_invar         :: Assertion
  } deriving Show

data LoopFusion = LoopFusion
  { lf_aloops   :: [Loop]
  , lf_eloops   :: [Loop]
  , lf_arest    :: [Program]
  , lf_erest    :: [Program]
  , lf_pre      :: Assertion
  , lf_post     :: Assertion
  , lf_origTrip :: RhleTriple
  , lf_invar    :: Assertion
  } deriving Show

data RevLoopFusion = RevLoopFusion
  { rlf_aloops   :: [RevLoop]
  , rlf_eloops   :: [RevLoop]
  , rlf_arest    :: [RevProgram]
  , rlf_erest    :: [RevProgram]
  , rlf_pre      :: Assertion
  , rlf_post     :: Assertion
  , rlf_origTrip :: RevRhleTriple
  , rlf_invar    :: Assertion
  } deriving Show
