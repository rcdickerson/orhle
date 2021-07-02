module Orhle.PredTransTypes
  ( Loop(..)
  , LoopFusion(..)
  ) where

import Ceili.Assertion ( Assertion(..) )
import Ceili.Language.FunImp
import Orhle.Triple

data Loop = Loop
  { l_body          :: FunImpProgram
  , l_condAssertion :: Assertion
  , l_condBExp      :: BExp
  , l_holeId        :: Maybe Int
  , l_invar         :: Assertion
  } deriving Show

data LoopFusion = LoopFusion
  { lf_aloops   :: [Loop]
  , lf_eloops   :: [Loop]
  , lf_arest    :: [FunImpProgram]
  , lf_erest    :: [FunImpProgram]
  , lf_pre      :: Assertion
  , lf_post     :: Assertion
  , lf_origTrip :: RhleTriple
  , lf_invar    :: Assertion
  } deriving Show
