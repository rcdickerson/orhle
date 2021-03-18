module Orhle.Imp
  ( AExp(..)
  , BExp(..)
  , FunImplEnv
  , ParseError
  , Program(..)
  , SFun(..)
  , Var
  , fillInvHole
  , invHoleIds
  , parseImp
  , ppProg
  , ppAExp
  , ppBExp
  ) where

import Data.Text ( unpack )
import Orhle.Imp.ImpLanguage
import Orhle.Imp.ImpParser
import Orhle.Imp.ImpPrettyPrint

ppProg :: Program -> String
ppProg = unpack . prettyprint

ppAExp :: AExp -> String
ppAExp = prettyprintAExp

ppBExp :: AExp -> String
ppBExp = prettyprintAExp
