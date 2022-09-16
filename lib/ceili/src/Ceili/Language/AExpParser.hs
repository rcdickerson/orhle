module Ceili.Language.AExpParser
  ( AExpParseable(..)
  , aexpLanguageDef
  , parseAExp
  ) where

import Ceili.Name ( Name(..) )
import qualified Ceili.Name as Name
import Ceili.Language.AExp
import Control.Monad ( liftM )
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

aexpLanguageDef :: LanguageDef a
aexpLanguageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter <|> char '@'
  , Token.identLetter     = alphaNum <|> char '_' <|> char '!'
  , Token.nestedComments  = True
  , Token.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames   = []
  , Token.reservedOpNames = ["+", "-", "*", "/", "%", "^"]
  }

lexer      = Token.makeTokenParser $ aexpLanguageDef
float      = Token.float      lexer
identifier = Token.identifier lexer
integer    = Token.integer    lexer
parens     = Token.parens     lexer
reservedOp = Token.reservedOp lexer


class AExpParseable t where
  getAExpParser :: Parsec String s t

instance AExpParseable Integer where
  getAExpParser = integer

instance AExpParseable Double where
  getAExpParser = float

type AExpParser s a = Parsec String s a

parseAExp :: AExpParseable t => AExpParser s (AExp t)
parseAExp = buildExpressionParser aOperators aTerm

aOperators = [ [Infix  (reservedOp "^" >> return APow) AssocLeft]
             , [Infix  (reservedOp "*" >> return AMul) AssocLeft,
                Infix  (reservedOp "/" >> return ADiv) AssocLeft,
                Infix  (reservedOp "%" >> return AMod) AssocLeft]
             , [Infix  (reservedOp "+" >> return AAdd) AssocLeft,
                Infix  (reservedOp "-" >> return ASub) AssocLeft]
              ]

aTerm :: AExpParseable t => AExpParser s (AExp t)
aTerm =  parens parseAExp
     <|> (name >>= return . AVar)
     <|> liftM ALit getAExpParser

name :: AExpParser s Name
name = identifier >>= (return . Name.fromString)
