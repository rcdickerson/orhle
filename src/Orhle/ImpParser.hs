-- A simple Imp parser with specified uninterpreted functions.
-- Based on https://wiki.haskell.org/Parsing_a_simple_imperative_language

module Orhle.ImpParser
    ( impParser
    , parseImp
    ) where

import Control.Monad
import Orhle.Assertion
import Orhle.AssertionParser
import Orhle.Imp
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: LanguageDef()
languageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter <|> char '@'
  , Token.identLetter     = alphaNum <|> char '_'
  , Token.nestedComments  = True
  , Token.opStart         = Token.opLetter languageDef
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames   = [ "if", "then", "else", "while", "do", "end"
                            , "call", "skip"
                            , "true", "false"
                            , "@inv", "@var"
                            , "local"
                            ]
  , Token.reservedOpNames = [ "+", "-", "*", "/", "%", "^"
                            , "==", "!=", "<=", ">=", "<", ">"
                            , "&&", "||", "!"
                            , ":="
                            ]
  }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
braces     = Token.braces     lexer
integer    = Token.integer    lexer
comma      = Token.comma      lexer
semi       = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer

type ImpParser a = Parsec String () a
type StmtParser  = ImpParser Stmt

parseImp :: String -> Either ParseError Stmt
parseImp = runParser impParser () ""

impParser :: StmtParser
impParser = do
  whiteSpace
  prog <- program
  return prog

program :: StmtParser
program = do
  stmts <- many1 $ statement
  case length stmts of
    1 -> return $ head stmts
    _ -> return $ SSeq  stmts

statement :: StmtParser
statement =   ifStmt
          <|> whileStmt
          <|> skipStmt
          <|> try funcStmt
          <|> assignStmt
          <|> parens statement

ifStmt :: StmtParser
ifStmt = do
  reserved "if"
  cond  <- bExpression
  reserved "then"
  tbranch <- many1 $ try statement
  reserved "else"
  ebranch <- many1 $ try statement
  reserved "end"
  return $ SIf cond (SSeq tbranch) (SSeq ebranch)

whileStmt :: StmtParser
whileStmt = do
  reserved "while"
  cond  <- bExpression
  whiteSpace
  reserved "do"
  (inv, local) <- option (ATrue, True) $ do
    reserved "@inv"
    local  <- option False $ do reserved "local"; return True
    invStr <- braces $ many $ noneOf "{}"
    case parseAssertion invStr of
      Left err  -> fail (show err)
      Right inv -> return (inv, local)
  var <- option (Num 0) $ do
    reserved "@var"
    varStr <- braces $ many $ noneOf "{}"
    case parseArith varStr of
      Left err  -> fail (show err)
      Right var -> return var
  whiteSpace
  body  <- many1 $ try statement
  whiteSpace
  reserved "end"
  let bodySeq = case body of
                  (stmt:[]) -> stmt
                  _         -> SSeq body
  let while = SWhile cond bodySeq (inv, var, local)
  return while

assignStmt :: StmtParser
assignStmt = do
  var  <- identifier
  reservedOp ":="
  expr <- aExpression
  semi
  return $ SAsgn var expr

funcStmt :: StmtParser
funcStmt = do
  assignees <- varArray
  reservedOp ":="
  reserved "call"
  funName <- identifier
  params  <- (liftM concat) . parens $ sepBy varArray comma
  whiteSpace
  semi
  return $ SCall assignees params funName

varArray :: ImpParser [Var]
varArray = do
  (vars, num) <- try (do
                         var <- identifier
                         char '[' >> whiteSpace
                         num <- integer
                         char ']' >> whiteSpace
                         return (var, num))
                     <|> (do var <- identifier; return (var, 0))
  return $ if (num == 0)
             then [vars]
             else map (\n -> vars ++ "_" ++ (show n)) [0..(num-1)]

skipStmt :: StmtParser
skipStmt = reserved "skip" >> semi >> return SSkip

aExpression :: ImpParser AExp
aExpression = buildExpressionParser aOperators aTerm

bExpression :: ImpParser BExp
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Infix  (reservedOp "^" >> return APow) AssocLeft]
             , [Infix  (reservedOp "*" >> return AMul) AssocLeft,
                Infix  (reservedOp "/" >> return ADiv) AssocLeft,
                Infix  (reservedOp "%" >> return AMod) AssocLeft]
             , [Infix  (reservedOp "+" >> return AAdd) AssocLeft,
                Infix  (reservedOp "-" >> return ASub) AssocLeft]
              ]

bOperators = [ [Prefix (reservedOp "!" >> return BNot)]
             , [Infix  (reservedOp "&&" >> return BAnd) AssocLeft,
                Infix  (reservedOp "||"  >> return BOr)  AssocLeft]
             ]

aTerm =  parens aExpression
     <|> liftM AVar identifier
     <|> liftM ALit integer

bTerm =  parens bExpression
     <|> (reserved "true"  >> return (BTrue ))
     <|> (reserved "false" >> return (BFalse))
     <|> (try $ bBinop "==" BEq)
     <|> (try $ bBinop "!=" BNe)
     <|> (try $ bBinop "<=" BLe)
     <|> (try $ bBinop ">=" BGe)
     <|> (try $ bBinop "<"  BLt)
     <|> (try $ bBinop ">"  BGt)

bBinop :: String -> (AExp -> AExp -> BExp) -> ImpParser BExp
bBinop opStr opFun = do
  lhs <- aExpression
  reservedOp opStr
  rhs <- aExpression
  return $ opFun lhs rhs
