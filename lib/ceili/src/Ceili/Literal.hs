{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Ceili.Literal
  ( CollectableLiterals(..)
  ) where

import Ceili.Language.Compose
import Data.Set ( Set )
import qualified Data.Set as Set

class CollectableLiterals e t where
  litsIn :: e -> Set t

instance (CollectableLiterals (f e) t, CollectableLiterals (g e) t) =>
         CollectableLiterals ((f :+: g) e) t where
  litsIn (Inl f) = litsIn f
  litsIn (Inr f) = litsIn f

instance (Ord t, CollectableLiterals a t) => CollectableLiterals [a] t where
  litsIn as = Set.unions $ map litsIn as
