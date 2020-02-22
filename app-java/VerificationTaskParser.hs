{-# OPTIONS_GHC -Wno-missing-signatures #-}

module VerificationTaskParser
  ( VerificationTask(..)
  , Execution(..)
  , parseVerificationTask
  )
where

import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token             as Token

type LoopLabel = String

data VerificationTask = VerificationTask
  { vtForallExecs :: [Execution]
  , vtExistsExecs :: [Execution]
  , vtPostCond    :: Maybe String
  , vtPreCond     :: Maybe String
  , vtLoopInvariants :: [(Execution, LoopLabel, String)]
  , vtLoopVariants :: [(Execution, LoopLabel, String)]
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
  loopInvariants <- option [] $ try $ conditionMap "loopInvariants"
  whiteSpace
  loopVariants <- option [] $ try $ conditionMap "loopVariants"
  whiteSpace
  eof
  return $ VerificationTask aExecs
                            eExecs
                            preCond
                            postCond
                            loopInvariants
                            loopVariants

conditionMap :: String -> VTParser [(Execution, LoopLabel, String)]
conditionMap name = do
  reserved name >> whiteSpace >> char ':' >> whiteSpace
  between (char '{') (char '}') (whiteSpace >> many loopLabeledCondition)

loopLabeledCondition :: VTParser (Execution, LoopLabel, String)
loopLabeledCondition = do
  e <- exec
  _ <- char '.'
  l <- identifier
  char ':' >> whiteSpace
  c <- condition
  return (e, l, c)

condition :: VTParser String
condition = do
  smtStr <- manyTill anyChar (try $ char ';')
  whiteSpace
  return smtStr

execs :: String -> VTParser [Execution]
execs keyword = do
  reserved keyword >> whiteSpace
  char ':' >> whiteSpace
  list <- exec `sepBy1` (char ',' >> whiteSpace)
  char ';' >> whiteSpace
  return list

exec :: VTParser Execution
exec = do
  name <- identifier
  eid  <- optionMaybe $ try execSubscriptParser
  whiteSpace
  return $ Execution name eid

execSubscriptParser :: VTParser String
execSubscriptParser = do
  whiteSpace >> char '[' >> whiteSpace
  eid <- many1 alphaNum
  whiteSpace >> char ']' >> whiteSpace
  return eid
