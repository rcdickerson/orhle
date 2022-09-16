{-# LANGUAGE TypeOperators #-}

module Ceili.PTS
  ( BackwardPT
  , ForwardPT
  ) where

import Ceili.Assertion ( Assertion )
import Ceili.CeiliEnv ( Ceili )

type BackwardPT c p t = c -> p -> Assertion t -> Ceili (Assertion t)
type ForwardPT  c p t = c -> p -> Assertion t -> Ceili (Assertion t)
