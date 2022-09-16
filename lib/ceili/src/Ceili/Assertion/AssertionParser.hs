module Ceili.Assertion.AssertionParser
  ( AssertionParseable(..)
  , ParseContext(..)
  , ParseError
  , arithParser
  , assertionParser
  , float
  , integer
  , parseArith
  , parseAssertion
  ) where

import           Ceili.Assertion.AssertionLanguage ( Arith, Assertion )
import qualified Ceili.Assertion.AssertionLanguage as A
import           Ceili.Name ( Name(..) )
import qualified Ceili.Name as Name
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: LanguageDef (ParseContext t)
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
                             "get-value", "model", "pop", "push", "set-info",
                             "set-logic", "set-option"
                            ]
  , Token.reservedOpNames = [ "+", "-", "*", "/"
                            , "=", ">=", "<=", "<", ">"
                            , "mod"
                            , "not", "and", "or"
                            ]
  }

lexer = Token.makeTokenParser languageDef

float      = Token.float      lexer
identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer
comma      = Token.comma      lexer
semi       = Token.semi       lexer
whitespace = Token.whiteSpace lexer


class AssertionParseable t where
  parseLiteral :: LiteralParser t
instance AssertionParseable Integer where
  parseLiteral = integer
instance AssertionParseable Double where
  parseLiteral = float

data ParseContext t = ParseContext { pc_literalParser :: LiteralParser t }

type LiteralParser t   = Parsec String (ParseContext t) t
type AssertionParser t = Parsec String (ParseContext t) (Assertion t)
type ArithParser t     = Parsec String (ParseContext t) (Arith t)
type NameParser t      = Parsec String (ParseContext t) Name

parseAssertion :: AssertionParseable t => String -> Either ParseError (Assertion t)
parseAssertion assertStr = runParser assertionParser (ParseContext parseLiteral) "" assertStr

parseArith :: AssertionParseable t => String -> Either ParseError (Arith t)
parseArith arithStr = runParser arithParser (ParseContext parseLiteral) "" arithStr

assertionParser :: AssertionParser t
assertionParser = whitespace >> (try model <|> boolExpr)

arithParser :: ArithParser t
arithParser = whitespace >> arithExpr

boolExpr :: AssertionParser t
boolExpr = try forall
       <|> try exists
       <|> try boolApp
       <|> try boolLit
       <|> boolVar

arithExpr :: ArithParser t
arithExpr = try arithApp
        <|> try arithLit
        <|> arithVar

name :: NameParser t
name = identifier >>= (return . Name.fromString)

boolLit :: AssertionParser t
boolLit = do
  b <- identifier
  whitespace
  case b of
    "true" -> return A.ATrue
    "false"-> return A.AFalse
    _       -> fail $ "expected a boolean literal, got: " ++ b

boolVar :: AssertionParser t
boolVar = do
  n <- name
  return $ A.Atom n

arithLit :: ArithParser t
arithLit = lit <|> parens lit

arithVar :: ArithParser t
arithVar = do
  n <- name
  whitespace
  return $ A.Var n

forall :: AssertionParser t
forall = do
  char '(' >> whitespace
  reserved "forall"
  vars <- parens $ many quantVar
  body <- boolExpr
  char ')' >> whitespace
  return $ A.Forall vars body

exists :: AssertionParser t
exists = do
  char '(' >> whitespace
  reserved "exists"
  vars <- parens $ many quantVar
  body <- boolExpr
  char ')' >> whitespace
  return $ A.Exists vars body

quantVar :: NameParser t
quantVar = do
  char '(' >> whitespace
  n <- name
  whitespace
  typ <- identifier
  char ')' >> whitespace
  return n

boolApp :: AssertionParser t
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

bArithApp2 :: String -> (Arith t -> Arith t -> Assertion t) -> AssertionParser t
bArithApp2 fname fun = do
  reserved fname >> whitespace
  operands <- many arithExpr
  applyFun operands
  where
    applyFun (a1 : a2 : []) = return $ fun a1 a2
    applyFun _ = fail $ fname ++ " takes two arguments"

boolApp1 :: String -> (Assertion t -> Assertion t) -> AssertionParser t
boolApp1 fname fun = do
  reserved fname >> whitespace
  operands <- many boolExpr
  applyFun operands
  where
    applyFun (a:[]) = return $ fun a
    applyFun _ = fail $ fname ++ " takes one argument"

boolApp2 :: String -> (Assertion t -> Assertion t -> Assertion t) -> AssertionParser t
boolApp2 fname fun = do
  reserved fname >> whitespace
  operands <- many boolExpr
  applyFun operands
  where
    applyFun (a1:a2:[]) = return $ fun a1 a2
    applyFun _ = fail $ fname ++ " takes two arguments"

boolAppN :: String -> ([Assertion t] -> Assertion t) -> AssertionParser t
boolAppN fname fun = do
  reserved fname >> whitespace
  operands <- many boolExpr
  return $ fun operands

arithApp :: ArithParser t
arithApp = do
  char '(' >> whitespace
  parsedApp <- do aArithAppN        "+"   A.Add
              <|> aArithAppAtLeast2 "-"   A.Sub
              <|> aArithAppN        "*"   A.Mul
              <|> aArithApp2        "/"   A.Div
              <|> aArithApp2        "^"   A.Pow
              <|> aArithApp2        "mod" A.Mod
  whitespace
  char ')' >> whitespace
  return parsedApp

lit :: ArithParser t
lit = do
  (ParseContext litParser) <- getState
  (return . A.Num) =<< litParser

aArithApp2 :: String -> (Arith t -> Arith t -> Arith t) -> ArithParser t
aArithApp2 fname fun = do
  reserved fname >> whitespace
  operands <- many arithExpr
  applyFun operands
  where
    applyFun (a1 : a2 : []) = return $ fun a1 a2
    applyFun _ = fail $ fname ++ " takes two arithmetical arguments"

aArithAppAtLeast2 :: String -> ([Arith t] -> Arith t) -> ArithParser t
aArithAppAtLeast2 fname fun = do
  reserved fname >> whitespace
  operands <- many arithExpr
  case operands of
    []   -> fail $ fname ++ " takes at least two arguments"
    _:[] -> fail $ fname ++ " takes at least two arguments"
    _ -> return $ fun operands

aArithAppN :: String -> ([Arith t] -> Arith t) -> ArithParser t
aArithAppN fname fun = do
  reserved fname >> whitespace
  operands <- many arithExpr
  return $ fun operands

model :: AssertionParser t
model = parens $ do
  reserved "model"
  defs <- many defineFun
  return $ case defs of
    [] -> A.ATrue
    (v, arith):[] -> A.Eq (A.Var v) arith
    _ -> A.And $ map (\(tn, arith) -> A.Eq (A.Var tn) arith) defs

defineFun :: Parsec String (ParseContext t) (Name, Arith t)
defineFun = parens $ do
  reserved "define-fun"
  funName <- name
  _ <- parens $ many name -- pararms currently unsupported
  typ <- identifier
  value <- arithExpr
  return (funName, value)
