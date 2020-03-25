{-# OPTIONS_GHC -Wno-missing-signatures #-}

module VerificationTaskParser
  ( VerificationTask(..)
  , Execution(..)
  , parseVerificationTask
  , parseFunSpecsFile
  )
where

import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token             as Token

import           Spec                           ( FunSpec(FunSpec) )

type LoopLabel = String

data VerificationTask = VerificationTask
  { vtForallExecs :: [Execution]
  , vtExistsExecs :: [Execution]
  , vtPreCond     :: String
  , vtPostCond    :: String
  , vtLoopInvariants :: [(Execution, LoopLabel, String)]
  , vtLoopVariants :: [(Execution, LoopLabel, String)]
  }
  deriving (Show)

data Execution = Execution
  { execProgramName :: String
  , execSubscript :: Maybe String
  }
  deriving (Show, Eq, Ord)

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

parens = Token.parens lexer
braces = Token.braces lexer
identifier = Token.identifier lexer
reserved = Token.reserved lexer
comma = Token.comma lexer
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
  preCond <- option "true" $ reservedLabel "pre" *> untilSemi
  whiteSpace
  postCond <- option "true" $ reservedLabel "post" *> untilSemi
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
  reserved name >> whiteSpace
  between (char '{') (char '}') (whiteSpace >> many loopLabeledCondition)

loopLabeledCondition :: VTParser (Execution, LoopLabel, String)
loopLabeledCondition = do
  e <- exec
  _ <- char '.'
  l <- identifier
  char ':' >> whiteSpace
  c <- untilSemi
  whiteSpace
  return (e, l, c)

untilSemi :: VTParser String
untilSemi = manyTill anyChar (try $ char ';')

execs :: String -> VTParser [Execution]
execs keyword = do
  reservedLabel keyword
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

parseFunSpecsFile
  :: String
  -> Either
       ParseError
       ([(String, FunSpec String)], [(String, FunSpec String)])
parseFunSpecsFile = runParser funSpecsFileParser () ""

funSpecsFileParser
  :: VTParser ([(String, FunSpec String)], [(String, FunSpec String)])
funSpecsFileParser = do
  whiteSpace
  aspecs <- option [] $ try $ funSpecList "aspecs"
  whiteSpace
  especs <- option [] $ try $ funSpecList "especs"
  whiteSpace
  eof
  return (aspecs, especs)

funSpecList :: String -> VTParser [(String, FunSpec String)]
funSpecList t = do
  reserved t
  whiteSpace
  braces (whiteSpace >> many funSpec)

funSpec :: VTParser (String, FunSpec String)
funSpec = do
  funName <- identifier
  params  <- parens (identifier `sepBy` comma)
  whiteSpace
  (templateVars, pre, post) <- braces $ do
    templateVars <- option [] $ do
      reservedLabel "templateVars"
      vars <- identifier `sepBy` comma
      _    <- char ';'
      return vars
    whiteSpace
    pre <- option "true" $ reservedLabel "pre" *> untilSemi
    whiteSpace
    post <- option "true" $ reservedLabel "post" *> untilSemi
    whiteSpace
    return (templateVars, pre, post)
  return (funName, FunSpec params templateVars pre post)


reservedLabel :: String -> VTParser ()
reservedLabel l = reserved l >> whiteSpace >> char ':' >> whiteSpace
