module Orhle.OrhleParser
  ( Exec(..)
  , ExecId
  , ExpectedResult(..)
  , parseOrhle
  ) where

import           Control.Monad
import qualified Data.Map              as Map
import           Orhle.Assertion        ( Assertion )
import qualified Orhle.Assertion       as A
import           Orhle.Imp
import qualified Orhle.MapNames        as Names
import           Orhle.Spec
import qualified Orhle.Spec            as S
import           Orhle.Triple
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token     as Token

data Exec = Forall String ExecId | Exists String ExecId
type ExecId = Maybe String
type NamedProg = (String, Program)

data ExpectedResult = ExpectSuccess | ExpectFailure
  deriving (Eq, Show)

languageDef :: LanguageDef()
languageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter
  , Token.identLetter     = alphaNum <|> char '_'
  , Token.nestedComments  = True
  , Token.opStart         = Token.opLetter languageDef
  , Token.opLetter        = oneOf ""
  , Token.reservedNames   = [ "aspecs", "especs"
                            , "pre", "post", "choiceVars"
                            , "prog", "endp"
                            , "expected", "invalid", "valid" ]
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

type OrhleAppParser a = Parsec String () a

parseOrhle :: String -> Either ParseError ([Exec], AESpecs, RhleTriple, ExpectedResult)
parseOrhle str = runParser orhleParser () "" str

orhleParser :: OrhleAppParser ([Exec], AESpecs, RhleTriple, ExpectedResult)
orhleParser = do
  whiteSpace
  expectedResult <- try expectedValid <|> expectedInvalid; whiteSpace

  aExecs  <- option [] $ try $ execs "forall" Forall; whiteSpace
  eExecs  <- option [] $ try $ execs "exists" Exists; whiteSpace

  pre  <- option A.ATrue $ labeledAssertion "pre"
  post <- option A.ATrue $ labeledAssertion "post"

  aSpecs <- option S.emptySpecMap $ do
    reserved "aspecs" >> whiteSpace >> char ':' >> whiteSpace
    specs <- many specification
    return $ Map.unions specs
  eSpecs <- option S.emptySpecMap $ do
    reserved "especs" >> whiteSpace >> char ':' >> whiteSpace
    specs <- many specification
    return $ Map.unions specs

  let prefixExecId specMap exec = S.prefixSpecs (execPrefix exec) specMap
  let prefixedASpecs = Map.unions $ map (prefixExecId aSpecs) aExecs
  let prefixedESpecs = Map.unions $ map (prefixExecId eSpecs) eExecs
  let specs = SpecMaps prefixedASpecs prefixedESpecs

  progs <- many program
  let lookupAndPrefix exec = case lookup (getExecName exec) progs of
        Nothing   -> fail $ "Program definition not found: " ++ (getExecName exec)
        Just prog -> return $ prefixProgram prog exec
  aProgs <- mapM lookupAndPrefix aExecs
  eProgs <- mapM lookupAndPrefix eExecs
  return $ ((aExecs ++ eExecs), specs, RhleTriple pre aProgs eProgs post, expectedResult)

prefixProgram :: Program -> Exec -> Program
prefixProgram prog exec = Names.prefix (execPrefix exec) prog

execPrefix :: Exec -> String
execPrefix exec = case (getExecId exec) of
                    Nothing  -> (getExecName exec) ++ "!"
                    Just eid -> (getExecName exec) ++ "!" ++ eid ++ "!"

untilSemi :: OrhleAppParser String
untilSemi = manyTill anyChar (try $ char ';')

expectedValid :: OrhleAppParser ExpectedResult
expectedValid = do
  reserved "expected" >> whiteSpace
  char ':' >> whiteSpace
  reserved "valid" >> whiteSpace
  semi >> whiteSpace
  return ExpectSuccess

expectedInvalid :: OrhleAppParser ExpectedResult
expectedInvalid = do
  reserved "expected" >> whiteSpace
  char ':' >> whiteSpace
  reserved "invalid" >> whiteSpace
  semi >> whiteSpace
  return ExpectFailure

execs :: String -> (String -> ExecId -> Exec) -> OrhleAppParser [Exec]
execs keyword quant = do
  reserved keyword >> whiteSpace
  char ':' >> whiteSpace
  execs <- sepBy1 (do
    name <- identifier
    eid  <- optionMaybe $ try execId
    whiteSpace
    return $ quant name eid) $ char ',' >> whiteSpace
  char ';' >> whiteSpace
  return execs

execId :: OrhleAppParser String
execId = do
  whiteSpace >> char '[' >> whiteSpace
  eid <- many1 alphaNum
  whiteSpace >> char ']' >> whiteSpace
  return eid

specification :: OrhleAppParser SpecMap
specification = do
  name   <- identifier
  params <- (liftM concat) . parens $ sepBy varArray comma
  whiteSpace >> char '{' >> whiteSpace
  choiceVars <- option [] $ do
    reserved "choiceVars" >> whiteSpace >> char ':' >> whiteSpace
    vars <- sepBy identifier comma
    whiteSpace >> char ';' >> whiteSpace
    return $ map (\v -> A.Ident v A.Int) vars
  pre  <- option A.ATrue $ labeledAssertion "pre"
  post <- option A.ATrue $ labeledAssertion "post"
  whiteSpace >> char '}' >> whiteSpace
  return $ S.addSpec name (Spec params choiceVars pre post) S.emptySpecMap

labeledAssertion :: String -> OrhleAppParser Assertion
labeledAssertion label = do
  reserved label >> whiteSpace >> char ':' >> whiteSpace
  str <- untilSemi
  whiteSpace
  case A.parseAssertion str of
    Left error      -> fail $ show error
    Right assertion -> return assertion

varArray :: OrhleAppParser [String]
varArray = do
  (vars, num) <- try (do
                         var <- identifier
                         char '[' >> whiteSpace
                         num <- integer
                         char ']' >> whiteSpace
                         return (var, num))
                     <|> (do var <- identifier; return (var, 0))
  return $ if (num == 0)
             then [vars]
             else map (\n -> vars ++ "_" ++ (show n)) [0..(num-1)]

program :: OrhleAppParser NamedProg
program = do
  reserved "prog"
  name <- identifier
  char '(' >> whiteSpace
  sepBy varArray comma
  whiteSpace
  char ')' >> whiteSpace >> char ':'
  progStr <- manyTill anyChar (try $ reserved "endp")
  whiteSpace
  case parseImp progStr of
    Left err ->   fail $ show err
    Right prog -> return (name, prog)

getExecName :: Exec -> String
getExecName (Forall name _) = name
getExecName (Exists name _) = name

getExecId :: Exec -> Maybe String
getExecId (Forall _ eid) = eid
getExecId (Exists _ eid) = eid
