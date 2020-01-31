module Spec
  ( ASTFunSpecMap
  , FunSpec(..)
  , FunSpecMap
  , FunSpecMaps(..)
  , StringFunSpecMap
  , addFunSpec
  , emptyFunSpec
  , funList
  , lookupFunSpec
  , prefixSpec
  , specAtCallsite
  , stringToASTSpec
  ) where

import qualified Data.Map as Map

import Imp
import SMTParser
import Z3.Monad
import Z3Util

data FunSpec a = FunSpec { params        :: [Var]
                         , templateVars  :: [Var]
                         , preCondition  :: a
                         , postCondition :: a
                         }

type FunSpecMap a     = Map.Map String (FunSpec a)
type StringFunSpecMap = FunSpecMap String
type ASTFunSpecMap    = FunSpecMap AST

data FunSpecMaps = FunSpecMaps
  { aspecs :: ASTFunSpecMap
  , especs :: ASTFunSpecMap
  }

emptyFunSpec :: FunSpecMap a
emptyFunSpec = Map.empty

addFunSpec :: String -> FunSpec a -> FunSpecMap a -> FunSpecMap a
addFunSpec = Map.insert

lookupFunSpec :: String -> FunSpecMap a -> Maybe (FunSpec a)
lookupFunSpec = Map.lookup

specAtCallsite :: [Var] -> [Var] -> String -> ASTFunSpecMap -> Z3 (Maybe ([Var], AST, AST))
specAtCallsite assignees cparams fName funSpecs = do
  case Map.lookup fName funSpecs of
    Nothing -> return Nothing
    Just (FunSpec fparams tvars pre post) -> do
      let rets = retVars $ length assignees
      let bind ast = substituteByName ast (rets ++ fparams) (assignees ++ cparams)
      boundPre  <- bind pre
      boundPost <- bind post
      return . Just $ (tvars, boundPre, boundPost)

retVars :: Int -> [Var]
retVars 0   = []
retVars 1   = ["!ret"]
retVars len = map (\i -> "!ret" ++ (show i)) [0..len]

prefixSpec :: String -> ASTFunSpecMap -> Z3 ASTFunSpecMap
prefixSpec prefix spec = traverse (\v -> prefixSpecs v)
                         $ Map.mapKeys (\k -> prefixFun k) spec
  where
    prefixFun fname  = prefix ++ fname
    prefixSpecs (FunSpec fparams tvars pre post) = do
      let prefixedFParams = map (\v -> prefix ++ v) fparams
      let prefixedTVars   = map (\v -> prefix ++ v) tvars
      prefixedPre  <- prefixAST pre
      prefixedPost <- prefixAST post
      return (FunSpec prefixedFParams prefixedTVars prefixedPre prefixedPost)
    prefixAST ast = do
      freeVars <- astFreeVars ast
      foldr subSymbol (return ast) freeVars
    subSymbol symbol z3AST = do
      ast  <- z3AST
      name <- getSymbolString symbol
      substituteByName ast [name] [prefix ++ name]

funList :: FunSpecMap a -> [String]
funList = Map.keys

stringToASTSpec :: StringFunSpecMap -> Either ParseError (Z3 ASTFunSpecMap)
stringToASTSpec = Map.foldrWithKey parse $ Right (return emptyFunSpec)
  where
    parse :: String -> (FunSpec String) -> Either ParseError (Z3 ASTFunSpecMap)
          -> Either ParseError (Z3 ASTFunSpecMap)
    parse fName (FunSpec fparams tvars preStr postStr) z3SpecOrError =
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
              return $ addFunSpec fName (FunSpec fparams tvars preAST postAST) spec
