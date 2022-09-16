{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Ceili.Evaluation
  ( Evaluable(..)
  ) where

import Ceili.Language.Compose
import Ceili.ProgState

class Evaluable ctx stateType expr val where
  eval :: ctx -> ProgState stateType -> expr -> val

instance ( Evaluable ctx st (f e) val
         , Evaluable ctx st (g e) val
         ) =>
         Evaluable ctx st ((f :+: g) e) val where
  eval c st (Inl f) = eval c st f
  eval c st (Inr g) = eval c st g
