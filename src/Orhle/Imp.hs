module Orhle.Imp
  ( AExp(..)
  , BExp(..)
  , CallId
  , FunImpl(..)
  , FunImplEnv
  , Name(..)
  , ParseError
  , Program(..)
  , aexpToArith
  , bexpToAssertion
  , filterEmpty
  , filterMaybeEmpty
  , headProg
  , headIsCall
  , headIsLoop
  , mapCallIds
  , parseImp
  , plits
  , ppProg
  , ppAExp
  , ppBExp
  ) where

import Data.Maybe ( catMaybes )
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

headProg :: Program -> (Program, Program)
headProg prog = case prog of
  SSkip        -> (prog, SSkip)
  SAsgn _ _    -> (prog, SSkip)
  SSeq []      -> (SSkip, SSkip)
  SSeq (s:ss)  -> let (s', ss') = headProg s
                      in case ss' of
                           SSkip -> (s', SSeq ss)
                           _     -> (s', SSeq $ ss':ss)
  SIf _ _ _    -> (prog, SSkip)
  SWhile _ _ _ -> (prog, SSkip)
  SCall _ _ _  -> (prog, SSkip)

headIsLoop :: Program -> Bool
headIsLoop prog = case headProg prog of
  (SWhile _ _ _, _) -> True
  _                 -> False

headIsCall :: Program -> Bool
headIsCall prog = case headProg prog of
  ((SCall _ _ _), _) -> True
  _                  -> False

filterEmpty :: [Program] -> [Program]
filterEmpty = catMaybes . (map filterMaybeEmpty)

filterMaybeEmpty :: Program -> Maybe Program
filterMaybeEmpty prog = case prog of
  SSkip            -> Nothing
  SAsgn _ _        -> Just prog
  SSeq []          -> Nothing
  SSeq ss          -> case catMaybes $ map filterMaybeEmpty ss of
                            []  -> Nothing
                            ss' -> Just $ SSeq ss'
  SIf _ _ _        -> Just prog
  SWhile c body iv -> (filterMaybeEmpty body) >>= \body' -> return $ SWhile c body' iv
  SCall _ _ _      -> Just prog
