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
parseSMT smt = runParser smtParser () "" smt

parseSMTOrError :: String -> Z3 AST
parseSMTOrError smt =
  case parseSMT smt of
    Left  err -> error $ "On input " ++ smt ++ "\nSMT parse error: " ++ (show err)
    Right ast -> ast

smtParser :: SMTParser AST
smtParser = sexp <|> lit

whitespace :: SMTParser ()
whitespace = do
  many $ oneOf " \n\t"
  return $ return ()

lit :: SMTParser AST
lit = smtInt <|> smtIdent <|> smtTrue <|> smtFalse

smtTrue :: SMTParser AST
smtTrue = string "true" >> whitespace >> return mkTrue

smtFalse :: SMTParser AST
smtFalse = string "false" >> whitespace >> return mkFalse

smtInt :: SMTParser AST
smtInt = do
  n <- many1 digit
  whitespace
  return $ mkInteger (read n)

smtIdent :: SMTParser AST
smtIdent = do
  start <- letter
  rest  <- many alphaNum
  whitespace
  return $ mkStringSymbol (start:rest) >>= mkIntVar

sexp :: SMTParser AST
sexp = do
  char '(' >> whitespace
  func <- funcDecl
  whitespace
  operands <- many smtParser
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
