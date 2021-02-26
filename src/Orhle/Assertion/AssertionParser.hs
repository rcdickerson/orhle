module Orhle.Assertion.AssertionParser
  ( ParseError
  , arithParser
  , assertionParser
  , parseArith
  , parseAssertion
  ) where

import Orhle.Assertion.AssertionLanguage ( Arith, Assertion )
import qualified Orhle.Assertion.AssertionLanguage as A
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: LanguageDef ()
languageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = ""
  , Token.commentEnd      = ""
  , Token.commentLine     = "//"
  , Token.identStart      = letter <|> char '_'
  , Token.identLetter     = alphaNum <|> char '_' <|> char '!' <|> char '.'
  , Token.nestedComments  = False
  , Token.opStart         = oneOf ":!#$%&*+/<=>?\\^|-~" -- No @ or . at start
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames = ["par", "NUMERAL", "DECIMAL", "STRING", "_", "!",
                             "as", "let", "forall", "exists", "assert",
                             "check-sat", "declare-fun", "declare-sort",
                             "define-fun", "define-sort", "exit",
                             "get-assertions", "get-assignment", "get-info",
                             "get-option", "get-proof", "set-unsat-core",
                             "get-value", "pop", "push", "set-info",
                             "set-logic", "set-option"
                            ]
  , Token.reservedOpNames = [ "+", "-", "*", "/"
                            , "=", ">=", "<=", "<", ">"
                            , "mod"
                            , "not", "and", "or"
                            ]
  }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer
comma      = Token.comma      lexer
semi       = Token.semi       lexer
whitespace = Token.whiteSpace lexer

type AssertionParser = Parsec String () Assertion
type ArithParser     = Parsec String () Arith
type IdentParser     = Parsec String () A.Ident
type SortParser      = Parsec String () A.Sort

parseAssertion :: String -> Either ParseError Assertion
parseAssertion assertStr = runParser assertionParser () "" assertStr

parseArith :: String -> Either ParseError Arith
parseArith arithStr = runParser arithParser () "" arithStr

assertionParser :: AssertionParser
assertionParser = whitespace >> boolExpr

arithParser :: ArithParser
arithParser = whitespace >> arithExpr

boolExpr :: AssertionParser
boolExpr = try forall <|> try exists <|> try boolApp <|> boolLit

arithExpr :: ArithParser
arithExpr = try arithApp <|> arithLit

boolLit :: AssertionParser
boolLit = do
  start <- letter
  rest  <- many $ alphaNum <|> char '!' <|> char '_'
  let name = start:rest
  whitespace
  return $ case name of
    "true"  -> A.ATrue
    "false" -> A.AFalse

arithLit :: ArithParser
arithLit = int <|> arithIdent

arithIdent :: ArithParser
arithIdent = do
  start <- letter
  rest  <- many $ alphaNum <|> char '!' <|> char '_'
  let name = start:rest
  whitespace
  return . A.Var $ A.Ident name A.Int

forall :: AssertionParser
forall = do
  char '(' >> whitespace
  reserved "forall"
  vars <- parens $ many quantVar
  body <- boolExpr
  char ')' >> whitespace
  return $ A.Forall vars body

exists :: AssertionParser
exists = do
  char '(' >> whitespace
  reserved "exists"
  vars <- parens $ many quantVar
  body <- boolExpr
  char ')' >> whitespace
  return $ A.Exists vars body

quantVar :: IdentParser
quantVar = do
  char '(' >> whitespace
  name <- identifier
  whitespace
  sort <- sortFromString =<< identifier
  char ')' >> whitespace
  return $ A.Ident name sort

sortFromString :: String -> SortParser
sortFromString "Int" = return A.Int
sortFromString s     = fail $ "Unknown sort: " ++ s

boolApp :: AssertionParser
boolApp = do
  char '(' >> whitespace
  parsedApp <- do (try $ bArithApp2 ">="  A.Gte)
              <|> (try $ bArithApp2 "<="  A.Lte)
              <|> (try $ boolApp2   "=>"  A.Imp)
              <|>        bArithApp2 ">"   A.Gt
              <|>        bArithApp2 "<"   A.Lt
              <|>        bArithApp2 "="   A.Eq
              <|>        boolAppN   "and" A.And
              <|>        boolApp1   "not" A.Not
              <|>        boolAppN   "or"  A.Or
  whitespace
  char ')' >> whitespace
  return parsedApp

bArithApp2 :: String -> (Arith -> Arith -> Assertion) -> AssertionParser
bArithApp2 name fun = do
  reserved name >> whitespace
  operands <- many arithExpr
  applyFun operands
  where
    applyFun (a1 : a2 : []) = return $ fun a1 a2
    applyFun _ = fail $ name ++ " takes two arguments"

boolApp1 :: String -> (Assertion -> Assertion) -> AssertionParser
boolApp1 name fun = do
  reserved name >> whitespace
  operands <- many boolExpr
  applyFun operands
  where
    applyFun (a:[]) = return $ fun a
    applyFun _ = fail $ name ++ " takes one argument"

boolApp2 :: String -> (Assertion -> Assertion -> Assertion) -> AssertionParser
boolApp2 name fun = do
  reserved name >> whitespace
  operands <- many boolExpr
  applyFun operands
  where
    applyFun (a1:a2:[]) = return $ fun a1 a2
    applyFun _ = fail $ name ++ " takes two arguments"

boolAppN :: String -> ([Assertion] -> Assertion) -> AssertionParser
boolAppN name fun = do
  reserved name >> whitespace
  operands <- many boolExpr
  return $ fun operands

arithApp :: ArithParser
arithApp = do
  char '(' >> whitespace
  parsedApp <- do aArithAppN "+"   A.Add
              <|> aArithAppN "-"   A.Sub
              <|> aArithAppN "*"   A.Mul
              <|> aArithApp2 "/"   A.Div
              <|> aArithApp2 "^"   A.Pow
              <|> aArithApp2 "mod" A.Mod
  whitespace
  char ')' >> whitespace
  return parsedApp

int :: ArithParser
int = do
  n <- many1 digit
  whitespace
  return $ A.Num (read n)

aArithApp2 :: String -> (Arith -> Arith -> Arith) -> ArithParser
aArithApp2 name fun = do
  reserved name >> whitespace
  operands <- many arithExpr
  applyFun operands
  where
    applyFun (a1 : a2 : []) = return $ fun a1 a2
    applyFun _ = fail $ name ++ " takes two arithmetical arguments"

aArithAppN :: String -> ([Arith] -> Arith) -> ArithParser
aArithAppN name fun = do
  reserved name >> whitespace
  operands <- many arithExpr
  return $ fun operands
