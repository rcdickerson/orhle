module Orhle.ShowSMT
  ( ShowSMT(..)
  ) where

class ShowSMT a where
  showSMT :: a -> String
