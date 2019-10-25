module SMTParser
  ( ParseError
  , parseSMT
  , parseSMTOrError
  , smtParser
  ) where

import Control.Monad
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import Z3.Monad

languageDef :: LanguageDef ()
languageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = ""
  , Token.commentEnd      = ""
  , Token.commentLine     = ";"
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
  , Token.reservedOpNames = [ "+", "-", "*"
                            , ":="
                            , "=="
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

type SMTParser a = Parsec String () (Z3 a)

data SMTFunc = SMTAnd
             | SMTEq
             | SMTImp
             | SMTGT
             | SMTGTE
             | SMTLT
             | SMTLTE
             | SMTMod
             | SMTNot
             | SMTOr

parseSMT :: String -> Either ParseError (Z3 AST)
parseSMT smt = runParser smtParser () "" smt

parseSMTOrError :: String -> Z3 AST
parseSMTOrError smt =
  case parseSMT smt of
    Left  err -> error $ "SMT parse error: " ++ (show err) ++ "\nOn input: " ++ smt
    Right ast -> ast

smtParser :: SMTParser AST
smtParser = whitespace >> smtExpr

smtExpr :: SMTParser AST
smtExpr = try smtSexpr <|> smtLit

smtLit :: SMTParser AST
smtLit = smtInt <|> smtIdent

smtInt :: SMTParser AST
smtInt = do
  n <- many1 digit
  whitespace
  return $ mkInteger (read n)

smtIdent :: SMTParser AST
smtIdent = do
  start <- letter
  rest  <- many $ alphaNum <|> char '!' <|> char '_'
  let id = start:rest
  whitespace
  return $ case id of
    "true"  -> mkTrue
    "false" -> mkFalse
    _       -> mkStringSymbol id >>= mkIntVar

smtSexpr :: SMTParser AST
smtSexpr = try smtForall <|> try smtExists <|> smtApp

smtForall :: SMTParser AST
smtForall = do
  char '(' >> whitespace
  reserved "forall"
  vars <- parens $ many smtQuantVar
  body <- smtExpr
  char ')' >> whitespace
  return $ constructForall vars body

smtExists :: SMTParser AST
smtExists = do
  char '(' >> whitespace
  reserved "exists"
  vars <- parens $ many smtQuantVar
  body <- smtExpr
  char ')' >> whitespace
  return $ constructExists vars body

smtQuantVar :: SMTParser (String, String)
smtQuantVar = do
  char '(' >> whitespace
  name <- identifier
  whitespace
  sort <- identifier
  char ')' >> whitespace
  return $ return (name, sort)

constructQuantVars :: [(String, String)] -> Z3 ([Symbol], [Sort])
constructQuantVars varDecls  = do
  vars <- sequence $ map mkQuantVar varDecls
  return $ unzip vars
  where
    mkQuantVar :: (String, String) -> Z3 (Symbol, Sort)
    mkQuantVar (symbName, sortName) = do
      symb     <- mkStringSymbol symbName
      sort     <- sortFromString sortName
      return (symb, sort)

sortFromString :: String -> Z3 Sort
sortFromString "Bool" = mkBoolSort
sortFromString "Int"  = mkIntSort
sortFromString "Real" = mkRealSort
sortFromString s = do
  sortSymb <- mkStringSymbol s
  mkUninterpretedSort sortSymb

constructForall :: [Z3 (String, String)] -> (Z3 AST) -> Z3 AST
constructForall decls body = do
  (symbs, sorts) <- constructQuantVars =<< sequence decls
  mkForall [] symbs sorts =<< body

constructExists :: [Z3 (String, String)] -> (Z3 AST) -> Z3 AST
constructExists decls body = do
  (symbs, sorts) <- constructQuantVars =<< sequence decls
  mkExists [] symbs sorts =<< body

smtApp :: SMTParser AST
smtApp = do
  char '(' >> whitespace
  func <- funcDecl
  whitespace
  operands <- many smtExpr
  whitespace
  char ')' >> whitespace
  return.join $ (liftM2 smtApply) func $ sequence operands

funcDecl :: SMTParser SMTFunc
funcDecl =     funcParser "and" SMTAnd
           <|> funcParser ">="  SMTGTE
           <|> funcParser "<="  SMTLTE
           <|> funcParser "=>"  SMTImp
           <|> funcParser ">"   SMTGT
           <|> funcParser "<"   SMTLT
           <|> funcParser "mod" SMTMod
           <|> funcParser "not" SMTNot
           <|> funcParser "or"  SMTOr
           <|> funcParser "="   SMTEq

smtApply :: SMTFunc -> [AST] -> Z3 AST
smtApply SMTAnd ops = mkAnd ops
smtApply SMTEq  (lhs:rhs:[]) = mkEq lhs rhs
smtApply SMTGT  (lhs:rhs:[]) = mkGt lhs rhs
smtApply SMTGTE (lhs:rhs:[]) = mkGe lhs rhs
smtApply SMTImp (lhs:rhs:[]) = mkImplies lhs rhs
smtApply SMTLT  (lhs:rhs:[]) = mkLt lhs rhs
smtApply SMTLTE (lhs:rhs:[]) = mkLe lhs rhs
smtApply SMTMod (lhs:rhs:[]) = mkMod lhs rhs
smtApply SMTNot (expr:[]) = mkNot expr
smtApply SMTOr ops = mkOr ops
smtApply SMTEq  _ = fail "equals takes exactly two arguments"
smtApply SMTGT  _ = fail "> takes exactly two arguments"
smtApply SMTGTE _ = fail ">= takes exactly two arguments"
smtApply SMTImp _ = fail "=> takes exactly two arguments"
smtApply SMTLT  _ = fail "< takes exactly two arguments"
smtApply SMTLTE _ = fail "<= takes exactly two arguments"
smtApply SMTMod _ = fail "mod takes exactly two arguments"
smtApply SMTNot _ = fail "not takes exactly one argument"

funcParser :: String -> SMTFunc -> SMTParser SMTFunc
funcParser str func = try $ string str >> whitespace >> (return $ return func)
