module KLiveParser
  ( KLExpectedResult(..)
  , KLQuery(..)
  , parseKLive
  ) where

import Orhle
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

data KLQuery = KLQuery
               { klPreCondSMT  :: String
               , klForallProgs :: [Prog]
               , klExistsProgs :: [Prog]
               , klPostCondSMT :: String
               }
data KLExpectedResult = KLSuccess | KLFailure

languageDef :: LanguageDef()
languageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "--"
  , Token.identStart      = letter
  , Token.identLetter     = alphaNum <|> char '_'
  , Token.nestedComments  = True
  , Token.opStart         = Token.opLetter languageDef
  , Token.opLetter        = oneOf ""
  , Token.reservedNames   = [ "end", "fails", "pre", "prog", "satisfies" ]
  , Token.reservedOpNames = [ ]
  }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer
comma      = Token.comma      lexer
semi       = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer

type KLiveParser a = Parsec String () a

data QExec = QEForall String | QEExists String
type NamedProg = (String, Prog)

parseKLive :: String -> Either ParseError (KLQuery, KLExpectedResult)
parseKLive str = runParser kliveParser () "" str

kliveParser :: KLiveParser (KLQuery, KLExpectedResult)
kliveParser = do
  whiteSpace
  preCond  <- preCondition
  char ':'
  execs    <- executions
  (postCond, expectedResult) <- postCondition
  progs <- many program
  let (aProgs, eProgs) = categorizeProgs execs progs
  return (KLQuery preCond aProgs eProgs postCond, expectedResult)

preCondition :: KLiveParser String
preCondition = do
  reserved "pre"
  char ':'
  return "<SMT>"

postCondition :: KLiveParser (String, KLExpectedResult)
postCondition = do
  expectedResult <- try expectedSat <|> expectedFail
  char ':'
  return ("<SMT>", expectedResult)

expectedSat :: KLiveParser KLExpectedResult
expectedSat = do
  reserved "satisfies"
  return KLSuccess

expectedFail :: KLiveParser KLExpectedResult
expectedFail = do
  reserved "fails"
  return KLFailure

executions :: KLiveParser [QExec]
executions = many1 (try forallExec <|> existsExec)

forallExec :: KLiveParser QExec
forallExec = do
  reserved "forall"
  name <- identifier
  return $ QEForall name

existsExec :: KLiveParser QExec
existsExec = do
  reserved "exists"
  name <- identifier
  return $ QEExists name

program :: KLiveParser NamedProg
program = do
  reserved "prog"
  name <- identifier
  char '(' >> char ')' -- TODO: Param lists?
  prog <- impParser
  reserved "end"
  return (name, prog)

categorizeProgs :: [QExec] -> [NamedProg] -> ([Prog], [Prog])
categorizeProgs execs namedProgs = foldr categorize ([], []) execs
  where
    categorize (QEForall name) (aProgs, eProgs) = (nappend name aProgs, eProgs)
    categorize (QEExists name) (aProgs, eProgs) = (aProgs, nappend name eProgs)
    nappend name progs =
      case lookup name namedProgs of
        Just prog -> prog:progs
        Nothing   -> fail $ "Program definition not found: " ++ name
