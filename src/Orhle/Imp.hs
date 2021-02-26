module Orhle.Imp
  ( AExp(..)
  , BExp(..)
  , ParseError
  , SFun(..)
  , Stmt(..)
  , Var
  , parseImp
  , ppStmt
  , ppAExp
  , ppBExp
  ) where

import Data.Text ( unpack )
import Orhle.Imp.ImpLanguage
import Orhle.Imp.ImpParser
import Orhle.Imp.ImpPrettyPrint

ppStmt :: Stmt -> String
ppStmt = unpack . prettyprint

ppAExp :: AExp -> String
ppAExp = prettyprintAExp

ppBExp :: AExp -> String
ppBExp = prettyprintAExp
