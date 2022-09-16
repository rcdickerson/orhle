module Ceili.Language.BExpParser
  ( bexpLanguageDef
  , parseBExp
  ) where

import Ceili.Name ( Name(..), fromString )
import Ceili.Language.BExp
import Ceili.Language.AExp
import Ceili.Language.AExpParser as AExpP
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

bexpLanguageDef :: LanguageDef a
bexpLanguageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter <|> char '@'
  , Token.identLetter     = alphaNum <|> char '_' <|> char '!'
  , Token.nestedComments  = True
  , Token.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames   = ["true", "false"]
  , Token.reservedOpNames = ["==", "!=", "<=", ">=", "<", ">"]
  }

lexer      = Token.makeTokenParser $ bexpLanguageDef
identifier = Token.identifier lexer
integer    = Token.integer    lexer
parens     = Token.parens     lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer

type BExpParser s a = Parsec String s a

parseBExp :: AExpParseable t => BExpParser s (BExp t)
parseBExp = buildExpressionParser bOperators bTerm

bOperators = [ [Prefix (reservedOp "!" >> return BNot)]
             , [Infix  (reservedOp "&&" >> return BAnd) AssocLeft,
                Infix  (reservedOp "||"  >> return BOr)  AssocLeft]
             ]

bTerm :: AExpParseable t => BExpParser s (BExp t)
bTerm = parens parseBExp
       <|> (reserved "true"  >> return (BTrue ))
       <|> (reserved "false" >> return (BFalse))
       <|> (try $ bBinop "==" BEq)
       <|> (try $ bBinop "!=" BNe)
       <|> (try $ bBinop "<=" BLe)
       <|> (try $ bBinop ">=" BGe)
       <|> (try $ bBinop "<"  BLt)
       <|> (try $ bBinop ">"  BGt)

bBinop :: AExpParseable t => String -> (AExp t -> AExp t -> BExp t) -> BExpParser s (BExp t)
bBinop opStr opFun = do
  lhs <- parseAExp
  reservedOp opStr
  rhs <- parseAExp
  return $ opFun lhs rhs

name :: BExpParser s Name
name = identifier >>= (return . fromString)
