module KLiveParser
  ( KLExpectedResult(..)
  , KLQuery(..)
  , QExec(..)
  , QExecId
  , parseKLive
  ) where

import qualified Data.Map as Map
import Orhle
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import Z3.Monad

data KLQuery = KLQuery
               { klSpec        :: ASTSpec
               , klPreCond     :: AST
               , klForallProgs :: [Prog]
               , klExistsProgs :: [Prog]
               , klPostCond    :: AST
               }

data QExec = QEForall String QExecId | QEExists String QExecId
type QExecId = Maybe String
type NamedProg = (String, (Prog, Z3 ASTSpec))

data KLExpectedResult = KLSuccess | KLFailure
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
  , Token.reservedNames   = [ "end", "expected", "invalid", "pre", "post", "prog", "valid" ]
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

parseKLive :: String -> Either ParseError ([QExec], Z3 KLQuery, KLExpectedResult)
parseKLive str = runParser kliveParser () "" str

kliveParser :: KLiveParser ([QExec], Z3 KLQuery, KLExpectedResult)
kliveParser = do
  whiteSpace
  aExecs  <- option [] $ try $ execs "forall" QEForall; whiteSpace
  eExecs  <- option [] $ try $ execs "exists" QEExists; whiteSpace
  preCond <- option mkTrue $ do
    reserved "pre" >> whiteSpace >> char ':' >> whiteSpace
    condition
  postCond <- option mkTrue $ do
    reserved "post" >> whiteSpace >> char ':' >> whiteSpace
    condition
  whiteSpace
  expectedResult <- try expectedValid <|> expectedInvalid; whiteSpace
  progs          <- many program
  let execs = aExecs ++ eExecs
  let (aProgs, eProgs, spec) = collateProgs execs progs
  let query = constructQuery spec preCond aProgs eProgs postCond
  return $ (execs, query, expectedResult)

constructQuery :: Z3 ASTSpec -> Z3 AST -> [Prog] -> [Prog] -> Z3 AST
               -> Z3 KLQuery
constructQuery z3Spec z3PreCond aProgs eProgs z3PostCond = do
  preCond  <- z3PreCond
  postCond <- z3PostCond
  astSpec  <- z3Spec
  return $ KLQuery astSpec preCond aProgs eProgs postCond

condition :: KLiveParser (Z3 AST)
condition = do
  smtStr <- manyTill anyChar (try $ char ';')
  whiteSpace
  case parseSMT smtStr of
    Left err  -> fail $ show err
    Right ast -> return ast

expectedValid :: KLiveParser KLExpectedResult
expectedValid = do
  reserved "expected" >> whiteSpace
  char ':' >> whiteSpace
  reserved "valid" >> whiteSpace
  semi >> whiteSpace
  return KLSuccess

expectedInvalid :: KLiveParser KLExpectedResult
expectedInvalid = do
  reserved "expected" >> whiteSpace
  char ':' >> whiteSpace
  reserved "invalid" >> whiteSpace
  semi >> whiteSpace
  return KLFailure

execs :: String -> (String -> QExecId -> QExec) -> KLiveParser [QExec]
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

execId :: KLiveParser String
execId = do
  whiteSpace >> char '[' >> whiteSpace
  eid <- many1 alphaNum
  whiteSpace >> char ']' >> whiteSpace
  return eid

program :: KLiveParser NamedProg
program = do
  reserved "prog"
  name <- identifier
  char '(' >> whiteSpace
  sepBy (identifier >> whiteSpace) $ char ',' >> whiteSpace
  char ')' >> whiteSpace >> char ':'
  progStr <- manyTill anyChar (try $ reserved "end")
  whiteSpace
  case parseImp progStr of
    Left err -> fail $ show err
    Right (prog, stringSpec) ->
      case (stringToASTSpec stringSpec) of
        Left err      -> fail $ show err
        Right astSpec -> return (name, (prog, astSpec))

getExecName :: QExec -> String
getExecName (QEForall name _) = name
getExecName (QEExists name _) = name

getExecId :: QExec -> Maybe String
getExecId (QEForall _ eid) = eid
getExecId (QEExists _ eid) = eid

collateProgs :: [QExec] -> [NamedProg] -> ([Prog], [Prog], Z3 ASTSpec)
collateProgs execs namedProgs = foldr progExecFolder ([], [], return emptyASTSpec) progExecs
  where
    progExecs :: [(QExec, Prog, Z3 ASTSpec)]
    progExecs = map progExec execs
    ----
    progExec :: QExec -> (QExec, Prog, Z3 ASTSpec)
    progExec exec = case lookup (getExecName exec) namedProgs of
      Nothing -> error $ "Program definition not found: " ++ (getExecName exec)
      Just (prog, spec) -> (exec, prog, spec)
    ----
    progExecFolder :: (QExec, Prog, Z3 ASTSpec)
                   -> ([Prog], [Prog], Z3 ASTSpec)
                   -> ([Prog], [Prog], Z3 ASTSpec)
    progExecFolder (exec, prog, z3ProgSpec) (aProgs, eProgs, z3Spec) =
      let prefix  = case (getExecId exec) of
                        Nothing  -> (getExecName exec) ++ "!"
                        Just eid -> (getExecName exec) ++ "!" ++ eid ++ "!"
          prog'   = prefixProgVars prefix prog
          z3Spec' = do spec     <- z3Spec
                       progSpec <- prefixSpec prefix =<< z3ProgSpec
                       return $ Map.union spec progSpec
      in case exec of
        (QEForall _ _) -> (prog':aProgs, eProgs,       z3Spec')
        (QEExists _ _) -> (aProgs,       prog':eProgs, z3Spec')
