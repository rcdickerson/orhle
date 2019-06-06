module Lib
    ( abduce
    , Abducible(..)
    , Abduction
    , AExp(..)
    , BExp(..)
    , bexpToCond
    , Cond(..)
    , condToZ3
    , conjoin
    , encodeImp
    , fPostCond
    , fPreCond
    , HLTrip(..)
    , HLETrip(..)
    , impParser
    , InterpMap(..)
    , InterpResult(..)
    , parseImp
    , parseImpOrError
    , putInterpMap
    , RHLETrip(..)
    , Stmt(..)
    , UFunc(..)
    , verify1
    , verify2
    , VResult(..)
    ) where

import Abduction
import Conditions
import Hoare
import HoareE
import Imp
import ImpParser
import RHLE
import Text.ParserCombinators.Parsec
import Verifier1
import Verifier2

parseImp :: String -> Either String Stmt
parseImp str = case parse impParser "" str of
    Left e  -> Left $ show e
    Right r -> Right r

parseImpOrError :: String -> Stmt
parseImpOrError str = case (parseImp str) of
  Left e -> error e
  Right stmt -> stmt
