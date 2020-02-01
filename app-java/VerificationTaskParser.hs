module VerificationTaskParser
  ( VerificationTask(..)
  , Execution(..)
  , parseVerificationTask
  )
where

import qualified Data.Map                      as Map
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token             as Token

data VerificationTask = VerificationTask
  { vtForallExecs :: [Execution]
  , vtExistsExecs :: [Execution]
  , vtPostCond    :: Maybe String
  , vtPreCond     :: Maybe String
  }
  deriving (Show)

data Execution = Execution
  { execProgramName :: String
  , execSubscript :: Maybe String
  }
  deriving (Show)

languageDef :: LanguageDef ()
languageDef = Token.LanguageDef { Token.caseSensitive   = True
                                , Token.commentStart    = "/*"
                                , Token.commentEnd      = "*/"
                                , Token.commentLine     = "//"
                                , Token.identStart      = letter
                                , Token.identLetter     = alphaNum <|> char '_'
                                , Token.nestedComments  = True
                                , Token.opStart = Token.opLetter languageDef
                                , Token.opLetter        = oneOf ""
                                , Token.reservedNames   = []
                                , Token.reservedOpNames = []
                                }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
integer = Token.integer lexer
comma = Token.comma lexer
semi = Token.semi lexer
whiteSpace = Token.whiteSpace lexer


type VTParser a = Parsec String () a

parseVerificationTask :: String -> Either ParseError VerificationTask
parseVerificationTask = runParser verificationTaskParser () ""

verificationTaskParser :: VTParser VerificationTask
verificationTaskParser = do
  whiteSpace
  aExecs <- option [] $ try $ execs "forall"
  whiteSpace
  eExecs <- option [] $ try $ execs "exists"
  whiteSpace
  preCond <- optionMaybe $ do
    reserved "pre" >> whiteSpace >> char ':' >> whiteSpace
    condition
  postCond <- optionMaybe $ do
    reserved "post" >> whiteSpace >> char ':' >> whiteSpace
    condition
  whiteSpace
  return $ VerificationTask aExecs eExecs preCond postCond

condition :: VTParser String
condition = do
  smtStr <- manyTill anyChar (try $ char ';')
  whiteSpace
  return smtStr

execs :: String -> VTParser [Execution]
execs keyword = do
  reserved keyword >> whiteSpace
  char ':' >> whiteSpace
  execs <-
    sepBy1
      (do
        name <- identifier
        eid  <- optionMaybe $ try execSubscriptParser
        whiteSpace
        return $ Execution name eid
      )
    $  char ','
    >> whiteSpace
  char ';' >> whiteSpace
  return execs

execSubscriptParser :: VTParser String
execSubscriptParser = do
  whiteSpace >> char '[' >> whiteSpace
  eid <- many1 alphaNum
  whiteSpace >> char ']' >> whiteSpace
  return eid
