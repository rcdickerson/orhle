module Orhle.OrhleParser
  ( Exec(..)
  , ExecId
  , ExpectedResult(..)
  , parseOrhle
  ) where

import           Control.Monad          ( liftM )
import qualified Data.Map              as Map
import           Orhle.Assertion        ( Assertion(..) )
import qualified Orhle.Assertion       as A
import qualified Orhle.Imp             as Imp
import           Orhle.Names            ( Name(..) )
import qualified Orhle.Names           as Names
import           Orhle.Spec             ( Spec(..) )
import qualified Orhle.Spec            as S
import           Orhle.Triple
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token     as Token

data Exec   = ExecForall String ExecId
            | ExecExists String ExecId
type ExecId = Maybe String

data ExpectedResult = ExpectSuccess | ExpectFailure
  deriving (Eq, Show)

languageDef :: LanguageDef Int
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

type OrhleAppParser a = Parsec String Int a

parseOrhle :: String -> Either ParseError ([Exec], Imp.FunImplEnv, S.AESpecs, RhleTriple, ExpectedResult)
parseOrhle str = runParser orhleParser 0 "" str

orhleParser :: OrhleAppParser ([Exec], Imp.FunImplEnv, S.AESpecs, RhleTriple, ExpectedResult)
orhleParser = do
  whiteSpace
  expectedResult <- option ExpectSuccess $
                    try expectedValid <|> expectedInvalid
  whiteSpace

  aExecs  <- option [] $ try $ execs "forall" ExecForall; whiteSpace
  eExecs  <- option [] $ try $ execs "exists" ExecExists; whiteSpace

  pre  <- option A.ATrue $ labeledAssertion "pre"
  post <- option A.ATrue $ labeledAssertion "post"

  aSpecs <- option S.emptySpecMap $ do
    reserved "aspecs" >> whiteSpace >> char ':' >> whiteSpace
    specs <- many $ try specification
    return $ Map.unions specs
  eSpecs <- option S.emptySpecMap $ do
    reserved "especs" >> whiteSpace >> char ':' >> whiteSpace
    specs <- many $ try specification
    return $ Map.unions specs

  let prefixExecId specMap exec = S.prefixSpecs (execPrefix exec) specMap
  let prefixedASpecs = Map.unions $ map (prefixExecId aSpecs) aExecs
  let prefixedESpecs = Map.unions $ map (prefixExecId eSpecs) eExecs
  let specs = S.AESpecs prefixedASpecs prefixedESpecs

  -- TODO: better is to compose the parser combinators
  rest <- manyTill anyChar eof
  funs <- case Imp.parseImp rest of
    Left err        -> fail $ show err
    Right (_, funs) -> return funs

  aProgs <- mapM (prefixedFunBody funs) aExecs
  eProgs <- mapM (prefixedFunBody funs) eExecs
  return $ ((aExecs ++ eExecs)
           , funs
           , specs
           , RhleTriple pre aProgs eProgs post
           , expectedResult)

prefixedFunBody :: Imp.FunImplEnv -> Exec -> OrhleAppParser Imp.Program
prefixedFunBody funs exec =
  let
    name     = getExecName exec
    exPrefix = execPrefix exec
  in case Map.lookup name funs of
    Nothing        -> fail   $ "Function definition not found: " ++ name
    Just (prog, _) -> return $ Names.prefix exPrefix prog

execPrefix :: Exec -> String
execPrefix exec =
  case (getExecId exec) of
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
  theExecs <- sepBy1 (do
    name <- identifier
    eid  <- optionMaybe $ try execId
    whiteSpace
    return $ quant name eid) $ char ',' >> whiteSpace
  char ';' >> whiteSpace
  return theExecs

execId :: OrhleAppParser String
execId = do
  whiteSpace >> char '[' >> whiteSpace
  eid <- many1 alphaNum
  whiteSpace >> char ']' >> whiteSpace
  return eid

specification :: OrhleAppParser S.SpecMap
specification = do
  funName <- identifier
  params <- (liftM concat) . parens $ sepBy varArray comma
  let paramNames = map (\n -> Name n 0) params
  whiteSpace >> char '{' >> whiteSpace
  choiceVars <- option [] $ do
    reserved "choiceVars" >> whiteSpace >> char ':' >> whiteSpace
    vars <- sepBy identifier comma
    whiteSpace >> char ';' >> whiteSpace
    return $ map (\v -> A.Ident (A.Name v 0) A.Int) vars
  pre  <- option A.ATrue $ labeledAssertion "pre"
  post <- option A.ATrue $ labeledAssertion "post"
  whiteSpace >> char '}' >> whiteSpace
  return $ S.addSpec (Name funName 0) (Spec paramNames choiceVars pre post) S.emptySpecMap

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

getExecName :: Exec -> String
getExecName (ExecForall name _) = name
getExecName (ExecExists name _) = name

getExecId :: Exec -> Maybe String
getExecId (ExecForall _ eid) = eid
getExecId (ExecExists _ eid) = eid
