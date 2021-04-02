-- A simple Imp parser with specified uninterpreted functions.
-- Based on https://wiki.haskell.org/Parsing_a_simple_imperative_language

module Orhle.Imp.ImpParser
    ( ParseError
    , parseImp
    , parseImpWithHoleIndex
    ) where

import           Control.Monad
import qualified Data.Map as Map
import           Data.Maybe ( catMaybes )
import           Orhle.Assertion.AssertionLanguage
import           Orhle.Assertion.AssertionParser
import           Orhle.Imp.ImpLanguage
import           Orhle.Name ( Name(..), namesIn )
import qualified Orhle.Name as Name
import           Text.Parsec
import           Text.Parsec.Expr
import           Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: LanguageDef ParseCtx
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
  , Token.reservedNames   = [ "if", "then", "else", "endif"
                            , "while", "do", "end"
                            , "@inv", "@var"
                            , "fun", "return", "call"
                            , "skip"
                            , "true", "false"
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

data ParseCtx = ParseCtx { ctxHoleId     :: Int
                         , ctxFunImplEnv :: FunImplEnv
                         } deriving Show

type ImpParser a   = Parsec String ParseCtx a
type ProgramParser = ImpParser Program

parseImp :: String -> Either ParseError (Program, FunImplEnv)
parseImp str = do
  (prog, _, funImpls) <- parseImpWithHoleIndex 0 str
  return (prog, funImpls)

parseImpWithHoleIndex :: Int -> String
                      -> Either ParseError (Program, Int, FunImplEnv)
parseImpWithHoleIndex holeId str = runParser impParser emptyCtx "" str
  where
    emptyCtx = ParseCtx holeId Map.empty
    impParser = do
      prog                     <- program
      ParseCtx holeId' funImpls <- getState
      return (prog, holeId', funImpls)

sseq :: [Program] -> Program
sseq stmts = case stmts of
  []   -> SSkip
  s:[] -> s
  ss   -> SSeq ss

program :: ProgramParser
program = do
  stmts <- (liftM catMaybes) . many1 $ do
    whiteSpace
    (funDef >> return Nothing) <|> (statement >>= return . Just)
  return $ sseq stmts

statement :: ProgramParser
statement =   ifStmt
          <|> whileStmt
          <|> skipStmt
          <|> (try funCall)
          <|> assignStmt
          <|> parens statement

ifStmt :: ProgramParser
ifStmt = do
  reserved "if"
  cond  <- bExpression
  reserved "then"
  tbranch <- many1 statement
  ebranch <- option [SSkip] $ (reserved "else" >>= \_ -> many1 statement)
  reserved "endif"
  return $ SIf cond (sseq tbranch) (sseq ebranch)

whileStmt:: ProgramParser
whileStmt = do
  reserved "while"
  cond  <- bExpression
  whiteSpace
  reserved "do"
  inv <- tryOrHole $ do
    reserved "@inv"
    invStr <- braces $ many $ noneOf "{}"
    case parseAssertion invStr of
      Left err  -> fail (show err)
      Right inv -> return inv
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
  let while = SWhile cond (sseq body) (inv, var)
  return while

name :: ImpParser Name
name = identifier >>= (return . Name.fromString)

tryOrHole :: (ImpParser Assertion) -> ImpParser Assertion
tryOrHole p = try p <|> hole

hole :: ImpParser Assertion
hole = do
  ParseCtx holeNum funImpls <- getState
  putState $ ParseCtx (holeNum + 1) funImpls
  return $ Hole holeNum

assignStmt :: ProgramParser
assignStmt = do
  var <- name
  reservedOp ":="
  expr <- aExpression
  _ <- semi
  return $ SAsgn var expr

funDef :: ImpParser ()
funDef = do
  reserved "fun"
  handle <- identifier
  params <- nameTuple
  (body, rets) <- braces (funBody handle)
  recordFunDef handle params body rets

funBody :: Name.Handle -> ImpParser (Program, [Name])
funBody cid = do
  bodyStmts <- many statement
  reserved "return"
  retExprs <- (try varArray)
          <|> (try $ aExpression >>= return . return)
          <|> aexpTuple
  _ <- semi
  let freshIds = Name.buildNextFreshIds $ namesIn (SSeq bodyStmts)
      retVal   = Name (cid ++ "!retVal") 0
      retNames = fst $ foldr (\_ (names, ids) ->
                                 let (nextFresh, ids') = Name.nextFreshName retVal ids
                                 in  (nextFresh:names, ids'))
                       ([], freshIds)
                       retExprs
      asgns    = map (uncurry SAsgn) $ zip retNames retExprs
      body     = bodyStmts ++ asgns
  return (sseq body, retNames)

funCall :: ProgramParser
funCall = do
  assignees <- (try nameTuple) <|> nameArray
  reservedOp ":="
  reserved "call"
  funName <- identifier
  args    <- aexpTuple
  _ <- semi
  return $ SCall funName args assignees

aexpTuple :: ImpParser [AExp]
aexpTuple = do
  args <- parens $ sepBy argument comma
  return $ concat args

argument :: ImpParser [AExp]
argument = varArray <|> (aExpression >>= return . return)

varArray :: ImpParser [AExp]
varArray = do
  names <- nameArray
  return $ map AVar names

nameTuple :: ImpParser [Name]
nameTuple = do
  names <- parens $ sepBy nameArray comma
  return $ concat names

nameArray :: ImpParser [Name]
nameArray = do
  (Name vname i, num) <- try (do
                         var <- name
                         char '[' >> whiteSpace
                         num <- integer
                         char ']' >> whiteSpace
                         return (var, num))
                     <|> (do var <- name; return (var, 0))
  return $ case num of
    0 -> [Name vname i]
    _ -> map (\n -> Name (vname ++ "_" ++ (show n)) i) [0..(num-1)]

skipStmt :: ProgramParser
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
     <|> (name >>= return . AVar)
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

recordFunDef :: Name.Handle -> [Name] -> Program -> [Name] -> ImpParser ()
recordFunDef handle params body rets = do
  ParseCtx holeId funs <- getState
  let funs' = Map.insert handle (FunImpl params body rets) funs
  putState $ ParseCtx holeId funs'
  return ()
