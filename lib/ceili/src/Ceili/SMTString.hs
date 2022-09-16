{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module Ceili.SMTString
  ( SMTString(..)
  , SMTTypeString(..)
  , showSMT
  ) where

import Data.ByteString ( ByteString )
import Data.ByteString.Char8 ( pack, unpack )

class SMTString a where
  toSMT   :: a -> ByteString

showSMT :: SMTString a => a -> String
showSMT = unpack . toSMT

instance SMTString a => SMTString (Maybe a) where
  toSMT Nothing  = pack "()"
  toSMT (Just x) = toSMT x

instance SMTString Integer where
  toSMT = pack . show

instance SMTString Bool where
  toSMT True  = pack "true"
  toSMT False = pack "false"

class SMTTypeString a where
  smtTypeString :: ByteString

instance SMTTypeString Integer where
  smtTypeString = pack "Int"

instance SMTTypeString Bool where
  smtTypeString = pack "Bool"
