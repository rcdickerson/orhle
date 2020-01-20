module InstructionsParser
  ( Instructions(..)
  , Execution(..)
  , parseInstructions
  )
where

import qualified Data.Map                      as Map
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token             as Token

data Instructions = Instructions
  { iForallExecs :: [Execution]
  , iExistsExecs :: [Execution]
  , iPostCond    :: Maybe String
  , iPreCond     :: Maybe String
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


type KLiveParser a = Parsec String () a

parseInstructions :: String -> Either ParseError Instructions
parseInstructions = runParser instructionsParser () ""

instructionsParser :: KLiveParser Instructions
instructionsParser = do
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
  return $ Instructions aExecs eExecs preCond postCond

condition :: KLiveParser String
condition = do
  smtStr <- manyTill anyChar (try $ char ';')
  whiteSpace
  return smtStr

execs :: String -> KLiveParser [Execution]
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

execSubscriptParser :: KLiveParser String
execSubscriptParser = do
  whiteSpace >> char '[' >> whiteSpace
  eid <- many1 alphaNum
  whiteSpace >> char ']' >> whiteSpace
  return eid
