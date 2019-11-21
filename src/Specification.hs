module Specification
  ( ASTFunSpec
  , FunSpec
  , StringFunSpec
  , addFunSpec
  , emptyFunSpec
  , lookupFunSpec
  , postCond
  , preCond
  , prefixSpec
  , stringToASTSpec
  , templateVars
  ) where

import qualified Data.Map as Map

import Imp
import SMTParser
import Z3.Monad
import Z3Util

type FunSpec a     = Map.Map SFun ([Var], a, a)
type StringFunSpec = FunSpec String
type ASTFunSpec    = FunSpec AST

emptyFunSpec :: FunSpec a
emptyFunSpec = Map.empty

addFunSpec :: SFun -> [Var] -> a -> a -> FunSpec a -> FunSpec a
addFunSpec func tvars pre post spec =
  Map.insert func (tvars, pre, post) spec

lookupFunSpec :: SFun -> FunSpec a -> Maybe ([Var], a, a)
lookupFunSpec = Map.lookup

templateVars :: SFun -> FunSpec a -> Maybe [Var]
templateVars func spec = Map.lookup func spec >>= \(tvars, _, _) -> return tvars

preCond :: SFun -> FunSpec a -> Maybe a
preCond func spec = Map.lookup func spec >>= \(_, pre, _) -> return pre

postCond :: SFun -> FunSpec a -> Maybe a
postCond func spec = Map.lookup func spec >>= \(_, _, post) -> return post

prefixSpec :: String -> ASTFunSpec -> Z3 ASTFunSpec
prefixSpec prefix spec = traverse (\v -> prefixSpecs v)
                         $ Map.mapKeys (\k -> prefixSFun k) spec
  where
    prefixSFun  (SFun n p)  = SFun (prefix ++ n) p
    prefixSpecs (tvars, pre, post) = do
      let prefixedTVars = map (\v -> prefix ++ v) tvars
      prefixedPre  <- prefixAST pre
      prefixedPost <- prefixAST post
      return (prefixedTVars, prefixedPre, prefixedPost)
    prefixAST ast = do
      freeVars <- astFreeVars ast
      foldr subSymbol (return ast) freeVars
    subSymbol symbol z3AST = do
      ast  <- z3AST
      name <- getSymbolString symbol
      substituteByName ast [name] [prefix ++ name]

stringToASTSpec :: StringFunSpec -> Either ParseError (Z3 ASTFunSpec)
stringToASTSpec = Map.foldrWithKey parse $ Right (return emptyFunSpec)
  where
    parse :: SFun -> ([Var], String, String) -> Either ParseError (Z3 ASTFunSpec)
          -> Either ParseError (Z3 ASTFunSpec)
    parse func (tvars, preStr, postStr) z3SpecOrError =
      case z3SpecOrError of
        l@(Left _)   -> l
        Right z3Spec ->
          case (parseSMT preStr, parseSMT postStr) of
            (Left e, _) -> Left $ e
            (_, Left e) -> Left $ e
            (Right z3Pre, Right z3Post) -> Right $ do
              preAST  <- z3Pre
              postAST <- z3Post
              spec    <- z3Spec
              return $ addFunSpec func tvars preAST postAST spec
