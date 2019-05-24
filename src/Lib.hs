module Lib
    ( abduce
    , Abducible(..)
    , Abduction
    , AExp(..)
    , BExp(..)
    , Cond(..)
    , condToZ3
    , conjoin
    , HLTrip(..)
    , HLETrip(..)
    , impParser
    , parseImp
    , parseImpOrError
    , RHLETrip(..)
    , setupAbduction
    , Stmt(..)
    , UFunc(..)
    , verify
    ) where

import Abduction
import Conditions
import Hoare
import HoareE
import Imp
import ImpParser
import RHLE
import Text.ParserCombinators.Parsec
import Verifier

parseImp :: String -> Either String Stmt
parseImp str = case parse impParser "" str of
    Left e  -> Left $ show e
    Right r -> Right r

parseImpOrError :: String -> Stmt
parseImpOrError str = case (parseImp str) of
  Left e -> error e
  Right stmt -> stmt
