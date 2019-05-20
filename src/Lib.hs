module Lib
    ( AExp(..)
    , BExp(..)
    , Cond(..)
    , condToZ3
    , HLTrip(..)
    , HLETrip(..)
    , impParser
    , parseImp
    , RHLETrip(..)
    , rhleVCs
    , Stmt(..)
    , UFunc(..)
    ) where

import Conditions
import Hoare
import HoareE
import Imp
import ImpParser
import RHLE
import Text.ParserCombinators.Parsec

parseImp :: String -> Either String Stmt
parseImp str = case parse impParser "" str of
    Left e  -> Left $ show e
    Right r -> Right r
