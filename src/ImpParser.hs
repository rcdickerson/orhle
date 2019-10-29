-- A simple Imp parser with specified uninterpreted functions.
-- Based on https://wiki.haskell.org/Parsing_a_simple_imperative_language

module ImpParser
    ( impParser
    , parseImp
    , parseImpOrError
    ) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Imp
import Specification
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: GenLanguageDef String () (StateT StringSpec Identity)
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

type ImpParser a = ParsecT String () (StateT StringSpec Identity) a

parseImp :: String -> Either ParseError (Prog, StringSpec)
parseImp str =
  let (prog, spec) = runIdentity $ runStateT (runPT impParser () "" str) emptyStringSpec
  in case prog of
    Left error -> Left error
    Right prog -> Right (prog, spec)

parseImpOrError :: String -> (Prog, StringSpec)
parseImpOrError str =
  case parseImp str of
    Left  err  -> error $ "Parse error: " ++ (show err)
    Right stmt -> stmt

impParser :: ImpParser Prog
impParser = do
  whiteSpace
  prog <- program
  return prog

program :: ImpParser Prog
program = do
  stmts <- many1 $ statement
  case length stmts of
    1 -> return $ head stmts
    _ -> return $ Seq  stmts

statement :: ImpParser Stmt
statement =   ifStmt
          <|> skipStmt
          <|> try funcStmt
          <|> assignStmt
          <|> parens statement

ifStmt :: ImpParser Stmt
ifStmt = do
  reserved "if"
  cond  <- bExpression
  reserved "then"
  stmt1 <- statement
  reserved "else"
  stmt2 <- statement
  semi
  return $ If cond stmt1 stmt2

assignStmt :: ImpParser Stmt
assignStmt = do
  var  <- identifier
  reservedOp ":="
  expr <- aExpression
  semi
  return $ var := expr

funcStmt :: ImpParser Stmt
funcStmt = do
  assignee <- identifier
  reservedOp ":="
  reserved "call"
  funcName <- identifier
  params   <- parens $ sepBy identifier comma
  let func = Func funcName params
  reserved "pre"
  pre <- between (char '{') (char '}') (many $ noneOf "{}")
  whiteSpace
  reserved "post"
  post <- between (char '{') (char '}') (many $ noneOf "{}")
  whiteSpace
  semi
  get >>= \spec -> put $ addSpec func pre post spec
  return $ Call assignee func

skipStmt :: ImpParser Stmt
skipStmt = reserved "skip" >> semi >> return Skip

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
