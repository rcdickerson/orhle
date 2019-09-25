module Specification
  ( Spec
  , addSpec
  , emptySpec
  , funSpec
  , postCond
  , preCond
  ) where

import qualified Data.Map as Map
import Imp
import Z3.Monad

type Spec = Map.Map Func (AST, AST)

emptySpec :: Spec
emptySpec = Map.empty

addSpec :: Func -> AST -> AST -> Spec -> Spec
addSpec func pre post spec =
  Map.insert func (pre, post) spec

preCond :: Func -> Spec -> Maybe AST
preCond func spec = Map.lookup func spec >>= return . fst

postCond :: Func -> Spec -> Maybe AST
postCond func spec = Map.lookup func spec >>= return . snd

funSpec :: Func -> Spec -> Maybe (AST, AST)
funSpec = Map.lookup
