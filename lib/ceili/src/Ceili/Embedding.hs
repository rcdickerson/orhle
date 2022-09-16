{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Ceili.Embedding
  ( Embeddable(..)
  ) where

class Embeddable a b where
  embed :: a -> b

instance Embeddable t t where
  embed = id
