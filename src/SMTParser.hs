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
             | SMTMod
             | SMTOr

parseSMT :: String -> Either ParseError (Z3 AST)
parseSMT smt = runParser smtExpr () "" smt

parseSMTOrError :: String -> Z3 AST
parseSMTOrError smt =
  case parseSMT smt of
    Left  err -> error $ "SMT parse error: " ++ (show err) ++ "\nOn input: " ++ smt
    Right ast -> ast

smtExpr :: SMTParser AST
smtExpr = try smtApp <|> smtLit

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
  rest  <- many alphaNum
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
           <|> funcParser "="   SMTEq
           <|> funcParser "mod" SMTMod
           <|> funcParser "or"  SMTOr

smtApply :: SMTFunc -> [AST] -> Z3 AST
smtApply SMTAnd ops = mkAnd ops
smtApply SMTEq (lhs:rhs:[]) = mkEq lhs rhs
smtApply SMTMod (lhs:rhs:[]) = mkMod lhs rhs
smtApply SMTOr ops = mkOr ops
-- TODO: something better than error
smtApply SMTEq _ = error "equals takes exactly two arguments"
smtApply SMTMod _ = error "mod takes exactly two arguments"

funcParser :: String -> SMTFunc -> SMTParser SMTFunc
funcParser str func = string str >> whitespace >> (return $ return func)
