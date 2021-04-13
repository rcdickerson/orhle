module Orhle.Assertion.AssertionParser
  ( ParseError
  , arithParser
  , assertionParser
  , parseArith
  , parseAssertion
  , parseGoals
  ) where

import           Data.Char ( toLower )
import           Data.Map  ( Map )
import qualified Data.Map as Map
import           Orhle.Assertion.AssertionLanguage ( Arith, Assertion )
import qualified Orhle.Assertion.AssertionLanguage as A
import           Orhle.Name ( Name(..), Type(..), TypedName(..) )
import qualified Orhle.Name as Name
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token as Token

languageDef :: LanguageDef Ctx
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
                             "set-logic", "set-option",
                             "goals", "goal"
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

---- Parse context ----
data Ctx = Ctx { ctx_letMapping :: Map String Assertion }

emptyCtx = Ctx Map.empty

ctxPutLetBinding :: String -> Assertion -> Parsec String Ctx ()
ctxPutLetBinding name assertion = do
  (Ctx letMapping) <- getState
  putState (Ctx $ Map.insert name assertion letMapping)

ctxGetLetBinding :: String -> Parsec String Ctx (Maybe Assertion)
ctxGetLetBinding name = do
  (Ctx letMapping) <- getState
  return $ Map.lookup name letMapping
-----------------------

type AssertionParser     = Parsec String Ctx Assertion
type AssertionListParser = Parsec String Ctx [Assertion]
type ArithParser         = Parsec String Ctx Arith
type GoalsParser         = Parsec String Ctx [[Assertion]]
type TNameParser         = Parsec String Ctx TypedName
type NameParser          = Parsec String Ctx Name
type TypeParser          = Parsec String Ctx Type

parseAssertion :: String -> Either ParseError Assertion
parseAssertion assertStr = runParser assertionParser emptyCtx "" assertStr

parseArith :: String -> Either ParseError Arith
parseArith arithStr = runParser arithParser emptyCtx "" arithStr

parseGoals :: String -> Either ParseError [[Assertion]]
parseGoals goalsStr = runParser goalsParser emptyCtx "" goalsStr

goalsParser :: GoalsParser
goalsParser = do
  whitespace >> char '(' >> whitespace
  reserved "goals"
  goals <- many goal
  whitespace >> char ')' >> whitespace
  return goals

goal :: AssertionListParser
goal = do
  whitespace >> char '(' >> whitespace
  reserved "goal"
  gs <- many assertionParser
  _  <- many annotation
  whitespace >> char ')' >> whitespace
  return gs

assertionParser :: AssertionParser
assertionParser = whitespace >> boolExpr

arithParser :: ArithParser
arithParser = whitespace >> arithExpr

letBinding :: AssertionParser
letBinding = parens $ do
  reserved "let"
  parens $ many $ do
    parens $ do
      name <- identifier
      whitespace
      expr <- boolExpr
      ctxPutLetBinding name expr
  body <- boolExpr
  return body

letRef :: AssertionParser
letRef = do
  binding <- ctxGetLetBinding =<< identifier
  case binding of
    Just a  -> return a
    Nothing -> fail $ "name not found"

boolExpr :: AssertionParser
boolExpr = try forall
       <|> try exists
       <|> try boolApp
       <|> try boolLit
       <|> try letBinding
       <|> try letRef
       <|> boolVar

annotation :: Parsec String Ctx (String, String)
annotation = do
  whitespace
  char ':'
  name <- identifier
  whitespace
  value <- (identifier <|> (integer >>= return . show))
  whitespace
  return (name, value)

arithExpr :: ArithParser
arithExpr = try arithApp
        <|> try arithLit
        <|> arithVar

name :: NameParser
name = identifier >>= (return . Name.fromString)

boolLit :: AssertionParser
boolLit = do
  b <- identifier
  whitespace
  case b of
    "true" -> return A.ATrue
    "false"-> return A.AFalse
    _       -> fail $ "expected a boolean literal, got: " ++ b

boolVar :: AssertionParser
boolVar = do
  n <- name
  return $ A.Atom $ TypedName n Bool

arithLit :: ArithParser
arithLit = int

arithVar :: ArithParser
arithVar = do
  n <- name
  whitespace
  return . A.Var $ TypedName n Int

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

quantVar :: TNameParser
quantVar = do
  char '(' >> whitespace
  n <- name
  whitespace
  ty <- typeFromString =<< identifier
  char ')' >> whitespace
  return $ TypedName n ty

typeFromString :: String -> TypeParser
typeFromString str = case map toLower str of
  "int" -> return Int
  _     -> fail $ "Unknown sort: " ++ str

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
int =
  (return . A.Num . fromIntegral) =<< integer

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
