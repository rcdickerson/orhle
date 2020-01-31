module KLiveParser
  ( KLExpectedResult(..)
  , KLQuery(..)
  , QExec(..)
  , QExecId
  , parseKLive
  ) where

import Control.Monad
import qualified Data.Map as Map
import Orhle
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import Z3.Monad

data KLQuery = KLQuery
               { klSpecs       :: FunSpecMaps
               , klPreCond     :: AST
               , klForallProgs :: [Prog]
               , klExistsProgs :: [Prog]
               , klPostCond    :: AST
               }

data QExec = QEForall String QExecId | QEExists String QExecId
type QExecId = Maybe String
type NamedProg = (String, ParsedProg)

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
  , Token.reservedNames   = [ "aspecs", "especs"
                            , "pre", "post", "templateVars"
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

type KLiveParser a = Parsec String () a

parseKLive :: String -> Either ParseError ([QExec], Z3 KLQuery, KLExpectedResult)
parseKLive str = runParser kliveParser () "" str

kliveParser :: KLiveParser ([QExec], Z3 KLQuery, KLExpectedResult)
kliveParser = do
  whiteSpace
  expectedResult <- try expectedValid <|> expectedInvalid; whiteSpace

  aExecs  <- option [] $ try $ execs "forall" QEForall; whiteSpace
  eExecs  <- option [] $ try $ execs "exists" QEExists; whiteSpace

  preCond <- option mkTrue $ do
    reserved "pre" >> whiteSpace >> char ':' >> whiteSpace
    condition
  whiteSpace
  postCond <- option mkTrue $ do
    reserved "post" >> whiteSpace >> char ':' >> whiteSpace
    condition
  whiteSpace

  aSpecList <- option [] $ do
    reserved "aspecs" >> whiteSpace >> char ':' >> whiteSpace
    many specification
  eSpecList <- option [] $ do
    reserved "especs" >> whiteSpace >> char ':' >> whiteSpace
    many specification
  let union specList = sequence specList >>= return . Map.unions
  let aSpecs = union aSpecList
  let eSpecs = union eSpecList
  let prefixSpecs z3Specs execs = do
        specs    <- z3Specs
        prefixed <- sequence $ map (\exec -> prefixSpec (execPrefix exec) specs) execs
        return $ Map.unions prefixed
  let prefixedASpecs = prefixSpecs aSpecs aExecs
  let prefixedESpecs = prefixSpecs eSpecs eExecs
  let specs = liftM2 FunSpecMaps prefixedASpecs prefixedESpecs

  progs  <- many program
  let lookupAndPrefix exec =
        case lookup (getExecName exec) progs of
          Nothing   -> error $ "Program definition not found: " ++ (getExecName exec)
          Just prog -> prefixProgram prog exec
  aProgs <- mapM lookupAndPrefix aExecs
  eProgs <- mapM lookupAndPrefix eExecs
  let query = liftM5 KLQuery specs preCond (sequence aProgs) (sequence eProgs) postCond
  return $ ((aExecs ++ eExecs), query, expectedResult)

prefixProgram :: ParsedProg -> QExec -> KLiveParser (Z3 Prog)
prefixProgram prog exec = do
  case parseLoopSpecs prog of
        Left parseError -> error  $ show parseError
        Right z3Prog    -> return $ prefixProgVars (execPrefix exec) =<< z3Prog

execPrefix :: QExec -> String
execPrefix exec = case (getExecId exec) of
                    Nothing  -> (getExecName exec) ++ "!"
                    Just eid -> (getExecName exec) ++ "!" ++ eid ++ "!"

untilSemi :: KLiveParser String
untilSemi = manyTill anyChar (try $ char ';')

condition :: KLiveParser (Z3 AST)
condition = do
  smtStr <- untilSemi
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

specification :: KLiveParser (Z3 ASTFunSpecMap)
specification = do
  name   <- identifier
  params <- parens $ sepBy identifier comma
  whiteSpace >> char '{' >> whiteSpace
  templateVars <- option [] $ do
    reserved "templateVars" >> whiteSpace >> char ':' >> whiteSpace
    vars <- sepBy identifier comma
    whiteSpace >> char ';' >> whiteSpace
    return vars
  pre <- option "true" $ do
    reserved "pre" >> whiteSpace >> char ':' >> whiteSpace
    untilSemi
  whiteSpace
  let z3Pre = case parseSMT pre of
        Left error -> fail $ show error
        Right smt  -> smt
  post <- option "true" $ do
    reserved "post" >> whiteSpace >> char ':' >> whiteSpace
    untilSemi
  whiteSpace
  let z3Post = case parseSMT post of
        Left error -> fail $ show error
        Right smt  -> smt
  whiteSpace >> char '}' >> whiteSpace
  return $ do
    pre <- z3Pre
    post <- z3Post
    return $ addFunSpec name (FunSpec params templateVars pre post) emptyFunSpec

program :: KLiveParser NamedProg
program = do
  reserved "prog"
  name <- identifier
  char '(' >> whiteSpace
  sepBy (identifier >> whiteSpace) $ char ',' >> whiteSpace
  char ')' >> whiteSpace >> char ':'
  progStr <- manyTill anyChar (try $ reserved "endp")
  whiteSpace
  case parseImp progStr of
    Left err ->   fail $ show err
    Right prog -> return (name, prog)

getExecName :: QExec -> String
getExecName (QEForall name _) = name
getExecName (QEExists name _) = name

getExecId :: QExec -> Maybe String
getExecId (QEForall _ eid) = eid
getExecId (QEExists _ eid) = eid

prefixProgVars :: String -> Prog -> Z3 Prog
prefixProgVars pre prog =
  case prog of
    SSkip          -> return $ SSkip
    SAsgn var aexp -> return $ SAsgn  (pre ++ var) (prefixA aexp)
    SSeq  stmts    -> do
      pstmts <- mapM (prefixProgVars pre) stmts
      return $ SSeq pstmts
    SIf cond s1 s2 -> do
      ps1 <- prefixProgVars pre s1
      ps2 <- prefixProgVars pre s2
      return $ SIf (prefixB cond) ps1 ps2
    SWhile cond body (inv, var, local) -> do
      pinv  <- prefixASTVars pre inv
      pvar  <- prefixASTVars pre var
      pbody <- prefixProgVars pre body
      return $ if local then SWhile (prefixB cond) pbody (pinv, pvar, local)
                        else SWhile (prefixB cond) pbody (inv,  pvar, local)
    SCall rets params fname -> return $ SCall (map prefix rets) (map prefix params) (prefix fname)
  where
    prefix s = pre ++ s
    prefixA = prefixAExpVars pre
    prefixB = prefixBExpVars pre
