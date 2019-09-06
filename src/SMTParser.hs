module SMTParser
  ( parseSMT
  , parseSMTOrError
  ) where

import Control.Monad
import Text.Parsec
import Z3.Monad

type SMTParser a = Parsec String () (Z3 a)

data SMTFunc = SMTAnd
             | SMTEq
             | SMTImp
             | SMTGTE
             | SMTLT
             | SMTMod
             | SMTNot
             | SMTOr

parseSMT :: String -> Either ParseError (Z3 AST)
parseSMT smt = runParser smtExpr () "" smt

parseSMTOrError :: String -> Z3 AST
parseSMTOrError smt =
  case parseSMT smt of
    Left  err -> error $ "SMT parse error: " ++ (show err) ++ "\nOn input: " ++ smt
    Right ast -> ast

smtExpr :: SMTParser AST
smtExpr = try smtApp <|> try smtLit

whitespace :: SMTParser ()
whitespace = do
  many $ oneOf " \n\t"
  return $ return ()

smtLit :: SMTParser AST
smtLit = smtParenedLit <|> smtInt <|> smtIdent

smtParenedLit :: SMTParser AST
smtParenedLit = do
  char '(' >> whitespace
  lit <- smtLit
  whitespace
  char ')' >> whitespace
  return lit

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
           <|> funcParser "=>"  SMTImp
           <|> funcParser "<"   SMTLT
           <|> funcParser "mod" SMTMod
           <|> funcParser "not" SMTNot
           <|> funcParser "or"  SMTOr
           <|> funcParser "="   SMTEq

smtApply :: SMTFunc -> [AST] -> Z3 AST
smtApply SMTAnd ops = mkAnd ops
smtApply SMTEq (lhs:rhs:[]) = mkEq lhs rhs
smtApply SMTGTE (lhs:rhs:[]) = mkGe lhs rhs
smtApply SMTImp (lhs:rhs:[]) = mkImplies lhs rhs
smtApply SMTLT (lhs:rhs:[]) = mkLt lhs rhs
smtApply SMTMod (lhs:rhs:[]) = mkMod lhs rhs
smtApply SMTNot (expr:[]) = mkNot expr
smtApply SMTOr ops = mkOr ops
-- TODO: something better than error
smtApply SMTEq _ = error "equals takes exactly two arguments"
smtApply SMTGTE _ = error ">= takes exactly two arguments"
smtApply SMTImp _ = error "=> takes exactly two arguments"
smtApply SMTLT _ = error "< takes exactly two arguments"
smtApply SMTMod _ = error "mod takes exactly two arguments"
smtApply SMTNot _ = error "not takes exactly one argument"

funcParser :: String -> SMTFunc -> SMTParser SMTFunc
funcParser str func = try $ string str >> whitespace >> (return $ return func)
