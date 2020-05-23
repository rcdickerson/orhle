module SMTParser
  ( ParseError
  , parseLoopSpecs
  , parseSMT
  , parseSMTOrError
  , smtParser
  ) where

import Control.Monad
import Data.Either
import Imp
import Text.Parsec
import Text.Parsec.Error
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import qualified SMTMonad as S
import qualified SMTLib2 as S

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

type ParsedStmt = AbsStmt String
type ParsedProg = ParsedStmt

type SMTParser a = Parsec String () (S.SMT a)

data SMTFunc = SMTAdd
             | SMTSub
             | SMTMul
             | SMTDiv
             | SMTPow
             | SMTAnd
             | SMTEq
             | SMTImp
             | SMTGT
             | SMTGTE
             | SMTLT
             | SMTLTE
             | SMTMod
             | SMTNot
             | SMTOr

parseSMT :: String -> Either ParseError (S.SMT S.Expr)
parseSMT smt = runParser smtParser () "" smt

parseSMTOrError :: String -> S.SMT S.Expr
parseSMTOrError smt =
  case parseSMT smt of
    Left  err -> error $ "SMT parse error: " ++ (show err) ++ "\nOn input: " ++ smt
    Right ast -> ast

parseLoopSpecs :: ParsedProg -> Either ParseError (S.SMT Prog)
parseLoopSpecs pprog =
  case pprog of
    SSkip                -> Right . return $ SSkip
    SAsgn var aexp       -> Right . return $ (SAsgn var aexp)
    SCall ret params fun -> Right . return $ (SCall ret params fun)
    SIf    cond s1 s2 -> mergeZ3Parse (parseLoopSpecs s1) (parseLoopSpecs s2)
                         (\s1' s2' -> return $ SIf cond s1' s2')
    SSeq   stmts      ->
      let (errors, parsed) = partitionEithers $ map parseLoopSpecs stmts
      in case errors of
        (e:es)  -> Left  $ foldr mergeError e es
        []      -> Right $ do stmts <- sequence parsed; return $ SSeq stmts
    SWhile cond body (inv, var, local) -> do
      case parseLoopSpecs body of
        Left err    -> Left err
        Right body' -> mergeZ3Parse (parseSMT inv) (parseSMT var)
                       (\invAST varAST -> do
                          body'' <- body'
                          return $ SWhile cond body'' (invAST, varAST, local))

mergeZ3Parse :: Either ParseError (S.SMT a)
             -> Either ParseError (S.SMT a)
             -> (a -> a -> S.SMT b)
             -> Either ParseError (S.SMT b)
mergeZ3Parse errOrRes1 errOrRes2 mergeRes =
  case (errOrRes1, errOrRes2) of
    (Left err1, Left err2) -> Left $ mergeError err1 err2
    (Left err1, _)         -> Left err1
    (_, Left err2)         -> Left err2
    (Right r1, Right r2)   -> Right $ do
      r1' <- r1
      r2' <- r2
      mergeRes r1' r2'

smtParser :: SMTParser S.Expr
smtParser = whitespace >> smtExpr

smtExpr :: SMTParser S.Expr
smtExpr = try smtSexpr <|> smtLit

smtLit :: SMTParser S.Expr
smtLit = smtInt <|> smtIdent

smtInt :: SMTParser S.Expr
smtInt = do
  n <- many1 digit
  whitespace
  return $ S.mkInteger (read n)

smtIdent :: SMTParser S.Expr
smtIdent = do
  start <- letter
  rest  <- many $ alphaNum <|> char '!' <|> char '_'
  let id = start:rest
  whitespace
  return $ case id of
    "true"  -> S.mkTrue
    "false" -> S.mkFalse
    _       -> S.mkStringSymbol id >>= S.mkIntVar

smtSexpr :: SMTParser S.Expr
smtSexpr = try smtForall <|> try smtExists <|> smtApp

smtForall :: SMTParser S.Expr
smtForall = do
  char '(' >> whitespace
  reserved "forall"
  vars <- parens $ many smtQuantVar
  body <- smtExpr
  char ')' >> whitespace
  return $ constructForall vars body

smtExists :: SMTParser S.Expr
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

constructQuantVars :: [(String, String)] -> S.SMT [S.Binder]
constructQuantVars varDecls  = do
  sequence $ map mkQuantVar varDecls
  where
    mkQuantVar :: (String, String) -> S.SMT S.Binder
    mkQuantVar (symbName, sortName) = do
      (S.Symbol symb) <- S.mkStringSymbol symbName
      sort <- sortFromString sortName
      return (S.Bind symb sort)

sortFromString :: String -> S.SMT S.Type
sortFromString "Bool" = S.mkBoolSort
sortFromString "Int"  = S.mkIntSort
sortFromString "Real" = S.mkRealSort
sortFromString s = do
  sortSymb <- S.mkStringSymbol s
  S.mkUninterpretedSort sortSymb

constructForall :: [S.SMT (String, String)] -> (S.SMT S.Expr) -> S.SMT S.Expr
constructForall decls body = do
  binders <- constructQuantVars =<< sequence decls
  return . S.Quant S.Forall binders =<< body

constructExists :: [S.SMT (String, String)] -> (S.SMT S.Expr) -> S.SMT S.Expr
constructExists decls body = do
  binders <- constructQuantVars =<< sequence decls
  return . S.Quant S.Exists binders =<< body

smtApp :: SMTParser S.Expr
smtApp = do
  char '(' >> whitespace
  func <- funcDecl
  whitespace
  operands <- many smtExpr
  whitespace
  char ')' >> whitespace
  return.join $ (liftM2 smtApply) func $ sequence operands

funcDecl :: SMTParser SMTFunc
funcDecl =     funcParser "+" SMTAdd
           <|> funcParser "-" SMTSub
           <|> funcParser "*" SMTMul
           <|> funcParser "/" SMTDiv
           <|> funcParser "^" SMTPow
           <|> (try $ funcParser ">="  SMTGTE)
           <|> (try $ funcParser "<="  SMTLTE)
           <|> (try $ funcParser "=>"  SMTImp)
           <|> funcParser ">"   SMTGT
           <|> funcParser "<"   SMTLT
           <|> funcParser "="   SMTEq
           <|> funcParser "mod" SMTMod
           <|> funcParser "and" SMTAnd
           <|> funcParser "not" SMTNot
           <|> funcParser "or"  SMTOr

funcParser :: String -> SMTFunc -> SMTParser SMTFunc
funcParser str func = reserved str >> (return $ return func)

smtApply :: SMTFunc -> [S.Expr] -> S.SMT S.Expr
smtApply SMTAdd ops = S.mkAdd ops
smtApply SMTSub ops = S.mkSub ops
smtApply SMTMul ops = S.mkMul ops
smtApply SMTDiv (lhs:rhs:[]) = S.mkDiv lhs rhs
smtApply SMTPow (base:pow:[]) = S.mkPower base pow
smtApply SMTAnd ops = S.mkAnd ops
smtApply SMTEq  (lhs:rhs:[]) = S.mkEq lhs rhs
smtApply SMTGT  (lhs:rhs:[]) = S.mkGt lhs rhs
smtApply SMTGTE (lhs:rhs:[]) = S.mkGe lhs rhs
smtApply SMTImp (lhs:rhs:[]) = S.mkImplies lhs rhs
smtApply SMTLT  (lhs:rhs:[]) = S.mkLt lhs rhs
smtApply SMTLTE (lhs:rhs:[]) = S.mkLe lhs rhs
smtApply SMTMod (lhs:rhs:[]) = S.mkMod lhs rhs
smtApply SMTNot (expr:[]) = S.mkNot expr
smtApply SMTOr ops = S.mkOr ops
smtApply SMTDiv _ = fail "divide takes exactly two arguments"
smtApply SMTPow _ = fail "exponentiation takes exactly two arguments"
smtApply SMTEq  _ = fail "equals takes exactly two arguments"
smtApply SMTGT  _ = fail "> takes exactly two arguments"
smtApply SMTGTE _ = fail ">= takes exactly two arguments"
smtApply SMTImp _ = fail "=> takes exactly two arguments"
smtApply SMTLT  _ = fail "< takes exactly two arguments"
smtApply SMTLTE _ = fail "<= takes exactly two arguments"
smtApply SMTMod _ = fail "mod takes exactly two arguments"
smtApply SMTNot _ = fail "not takes exactly one argument"
