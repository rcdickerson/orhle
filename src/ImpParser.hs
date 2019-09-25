-- A simple Imp parser with specified uninterpreted functions.
-- Based on https://wiki.haskell.org/Parsing_a_simple_imperative_language

module ImpParser
    ( parseImp
    , parseImpOrError
    ) where

import Control.Monad
import Imp
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: LanguageDef ()
languageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter
  , Token.identLetter     = alphaNum <|> char '_'
  , Token.nestedComments  = True
  , Token.opStart         = Token.opLetter languageDef
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames   = [ "if", "then", "else"
                            , "call", "pre", "post"
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

type ImpParser a = Parsec String () a

parseImp :: String -> Either ParseError Prog
parseImp str = runParser impParser () "" str

parseImpOrError :: String -> Prog
parseImpOrError str =
  case parseImp str of
    Left  err  -> error $ "Parse error: " ++ (show err)
    Right stmt -> stmt

impParser :: ImpParser Prog
impParser = whiteSpace >> statement

statement :: ImpParser Stmt
statement = parens statement <|> sequenceOfStmt

sequenceOfStmt :: ImpParser Stmt
sequenceOfStmt = do
  list <- sepBy1 statement' semi
  case length list of
    1 -> return $ head list
    _ -> return $ Seq list

statement' :: ImpParser Stmt
statement' =   ifStmt
           <|> skipStmt
           <|> assignStmt
           <|> funcStmt

ifStmt :: ImpParser Stmt
ifStmt = do
  reserved "if"
  cond  <- bExpression
  reserved "then"
  stmt1 <- statement
  reserved "else"
  stmt2 <- statement
  return $ If cond stmt1 stmt2

assignStmt :: ImpParser Stmt
assignStmt = do
  var  <- identifier
  reservedOp ":="
  expr <- aExpression
  return $ var := expr

funcStmt :: ImpParser Stmt
funcStmt = do
  reserved "call"
  assignee <- identifier
  reservedOp ":="
  funcName <- identifier
  params <- parens $ sepBy identifier comma
  reserved "pre"
  pre <- between (char '{') (char '}') (many $ noneOf "{}")
  whiteSpace
  reserved "post"
  post <- between (char '{') (char '}') (many $ noneOf "{}")
  whiteSpace
  -- TODO: Return a Spec as well to continue allowing inline specs?
  return $ Call assignee (Func funcName params)

skipStmt :: ImpParser Stmt
skipStmt = reserved "skip" >> return Skip

aExpression :: ImpParser AExp
aExpression = buildExpressionParser aOperators aTerm

bExpression :: ImpParser BExp
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
