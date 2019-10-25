{-# LANGUAGE QuasiQuotes #-}

module Specification
  ( Spec
  , ASTSpec
  , StringSpec
  , addSpec
  , emptyASTSpec
  , emptyStringSpec
  , funSpec
  , postCond
  , preCond
  , prefixSpec
  , stringToASTSpec
  ) where

import qualified Data.Map as Map

import Imp
import SMTParser
import Z3.Monad
import Z3Util

type Spec a     = Map.Map Func (a, a)
type StringSpec = Spec String
type ASTSpec    = Spec AST

emptyStringSpec :: StringSpec
emptyStringSpec = Map.empty

emptyASTSpec :: ASTSpec
emptyASTSpec = Map.empty

addSpec :: Func -> a -> a -> Spec a -> Spec a
addSpec func pre post spec =
  Map.insert func (pre, post) spec

preCond :: Func -> Spec a -> Maybe a
preCond func spec = Map.lookup func spec >>= return . fst

postCond :: Func -> Spec a -> Maybe a
postCond func spec = Map.lookup func spec >>= return . snd

funSpec :: Func -> Spec a -> Maybe (a, a)
funSpec = Map.lookup

prefixSpec :: String -> ASTSpec -> Z3 ASTSpec
prefixSpec prefix spec = traverse (\v -> prefixSpecs v)
                         $ Map.mapKeys (\k -> prefixFunc k) spec
  where
    prefixFunc  (Func n p)  = Func (prefix ++ n) p
    prefixSpecs (pre, post) = do
      prefixedPre  <- prefixAST pre
      prefixedPost <- prefixAST post
      return (prefixedPre, prefixedPost)
    prefixAST ast = do
      freeVars <- astFreeVars ast
      foldr subSymbol (return ast) freeVars
    subSymbol symbol z3AST = do
      ast  <- z3AST
      name <- getSymbolString symbol
      substituteByName ast [name] [prefix ++ name]

stringToASTSpec :: StringSpec -> Either ParseError (Z3 ASTSpec)
stringToASTSpec = Map.foldrWithKey parse $ Right (return emptyASTSpec)
  where
    parse :: Func -> (String, String) -> Either ParseError (Z3 ASTSpec)
          -> Either ParseError (Z3 ASTSpec)
    parse func (preStr, postStr) z3SpecOrError =
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
              return $ addSpec func preAST postAST spec
