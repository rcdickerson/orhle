module Orhle.SMTString
  ( SMTString(..)
  , showSMT
  ) where

import Data.ByteString ( ByteString )
import Data.ByteString.Char8 ( unpack )

class SMTString a where
  toSMT :: a -> ByteString

showSMT :: SMTString a => a -> String
showSMT = unpack . toSMT
