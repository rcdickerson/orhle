-- A simple Imp parser with specified uninterpreted functions.
-- Based on https://wiki.haskell.org/Parsing_a_simple_imperative_language

module ImpParser
    ( ParsedProg
    , ParsedStmt
    , impParser
    , parseImp
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

languageDef :: GenLanguageDef String () (StateT StringFunSpec Identity)
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
                            , "@templateVars", "@pre", "@post", "@inv", "@var"
                            , "local"
                            ]
  , Token.reservedOpNames = [ "+", "-", "*", "/", "%"
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

type ParsedStmt = AbsStmt String
type ParsedProg = ParsedStmt

type ImpParser a = ParsecT String () (StateT StringFunSpec Identity) a

parseImp :: String -> Either ParseError (ParsedProg, StringFunSpec)
parseImp str =
  let (prog, spec) = runIdentity $
        runStateT (runPT impParser () "" str) emptyFunSpec
  in case prog of
    Left error -> Left error
    Right prog -> Right (prog, spec)

impParser :: ImpParser ParsedProg
impParser = do
  whiteSpace
  prog <- program
  return prog

program :: ImpParser ParsedProg
program = do
  stmts <- many1 $ statement
  case length stmts of
    1 -> return $ head stmts
    _ -> return $ SSeq  stmts

statement :: ImpParser ParsedStmt
statement =   ifStmt
          <|> whileStmt
          <|> skipStmt
          <|> try funcStmt
          <|> assignStmt
          <|> parens statement

ifStmt :: ImpParser ParsedStmt
ifStmt = do
  reserved "if"
  cond  <- bExpression
  reserved "then"
  tbranch <- many1 $ try statement
  reserved "else"
  ebranch <- many1 $ try statement
  reserved "end"
  return $ SIf cond (SSeq tbranch) (SSeq ebranch)

whileStmt :: ImpParser ParsedStmt
whileStmt = do
  reserved "while"
  cond  <- bExpression
  whiteSpace
  reserved "do"
  (inv, local) <- option ("true", True) $ do
    reserved "@inv"
    local <- option False $ do reserved "local"; return True
    inv <- braces $ many $ noneOf "{}"
    return (inv, local)
  var <- option "true" $ do
    reserved "@var"
    braces $ many $ noneOf "{}"
  whiteSpace
  body  <- many1 $ try statement
  whiteSpace
  reserved "end"
  let bodySeq = case body of
                  (stmt:[]) -> stmt
                  _         -> SSeq body
  let while = SWhile cond bodySeq (inv, var, local)
  return while

assignStmt :: ImpParser ParsedStmt
assignStmt = do
  var  <- identifier
  reservedOp ":="
  expr <- aExpression
  semi
  return $ SAsgn var expr

funcStmt :: ImpParser ParsedStmt
funcStmt = do
  (assignee, num) <- try (do
                             id <- identifier
                             char '[' >> whiteSpace
                             num <- integer
                             char ']' >> whiteSpace
                             return (id, num))
                     <|> (do id <- identifier; return (id, 0))
  let assignees = if (num == 0)
                  then [assignee]
                  else map (\n -> assignee ++ "_" ++ (show n)) [0..(num-1)]
  reservedOp ":="
  reserved "call"
  funcName <- identifier
  params   <- parens $ sepBy identifier comma
  whiteSpace
  tvars <- option [] $ do
    reserved "@templateVars"
    braces $ sepBy identifier comma
  whiteSpace
  pre <- option "true" $ do
    reserved "@pre"
    braces $ many $ noneOf "{}"
  whiteSpace
  post <- option "true" $ do
    reserved "@post"
    braces $ many $ noneOf "{}"
  whiteSpace
  semi
  let func = SFun funcName params
  get >>= \spec -> put $ addFunSpec func tvars pre post spec
  return $ SCall assignees func

skipStmt :: ImpParser ParsedStmt
skipStmt = reserved "skip" >> semi >> return SSkip

aExpression :: ImpParser AExp
aExpression = buildExpressionParser aOperators aTerm

bExpression :: ImpParser BExp
bExpression = buildExpressionParser bOperators bTerm

aOperators = [ [Infix  (reservedOp "*" >> return AMul) AssocLeft,
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
