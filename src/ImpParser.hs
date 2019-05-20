-- A simple Imp parser (with specified uninterpreted functions).
-- Based on https://wiki.haskell.org/Parsing_a_simple_imperative_language

module ImpParser
    ( impParser
    ) where

import Control.Monad
import Imp
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

languageDef = emptyDef { Token.identStart      = letter
                       , Token.identLetter     = alphaNum
                       , Token.reservedNames   = [ "if", "then", "else"
                                                 , "func", "pre", "post"
                                                 , "skip"
                                                 , "true"
                                                 , "false"
                                                 , "not"
                                                 , "and"
                                                 , "or"
                                                 ]
                       , Token.reservedOpNames = [ "+", "-", "*"
                                                 , ":="
                                                 , "=="
                                                 , "%"
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
whiteSpace = Token.whiteSpace lexer

impParser :: Parser Stmt
impParser = whiteSpace >> statement

statement :: Parser Stmt
statement = parens statement <|> sequenceOfStmt

sequenceOfStmt :: Parser Stmt
sequenceOfStmt = do
  list <- sepBy1 statement' semi
  return $ if length list == 1 then head list else Seq list

statement' :: Parser Stmt
statement' =   ifStmt
           <|> skipStmt
           <|> assignStmt
           <|> funcStmt

ifStmt :: Parser Stmt
ifStmt = do
  reserved "if"
  cond  <- bExpression
  reserved "then"
  stmt1 <- statement
  reserved "else"
  stmt2 <- statement
  return $ If cond stmt1 stmt2

assignStmt :: Parser Stmt
assignStmt = do
  var  <- identifier
  reservedOp ":="
  expr <- aExpression
  return $ var := expr

funcStmt :: Parser Stmt
funcStmt = do
  reserved "func"
  funcName <- identifier
  params <- parens $ sepBy1 identifier comma
  reserved "pre"
  pre <- bExpression
  reserved "post"
  post <- bExpression
  return $ Call (UFunc funcName params pre post)

skipStmt :: Parser Stmt
skipStmt = reserved "skip" >> return Skip

aExpression :: Parser AExp
aExpression = buildExpressionParser aOperators aTerm

bExpression :: Parser BExp
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Infix  (reservedOp "*" >> return (:*: )) AssocLeft,
                Infix  (reservedOp "%" >> return (AMod)) AssocLeft]
             , [Infix  (reservedOp "+" >> return (:+: )) AssocLeft,
                Infix  (reservedOp "-" >> return (:-: )) AssocLeft]
              ]

bOperators = [ [Prefix (reservedOp "not" >> return (BNot))]
             , [Infix  (reservedOp "and" >> return (BAnd)) AssocLeft,
                Infix  (reservedOp "or"  >> return (BOr )) AssocLeft]
             ]

aTerm =  parens aExpression
     <|> liftM V identifier
     <|> liftM I integer

bTerm =  parens bExpression
     <|> (reserved "true"  >> return (BTrue ))
     <|> (reserved "false" >> return (BFalse))
     <|> do lhs <- aExpression
            reservedOp "=="
            rhs <- aExpression
            return $ lhs :=: rhs
