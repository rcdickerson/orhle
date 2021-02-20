module OrhleAppParser
  ( OAExpectedResult(..)
  , OAQuery(..)
  , OAExec(..)
  , OAExecId
  , parseOrhleApp
  ) where

import           Control.Monad
import qualified Data.Map             as Map
import           Imp
import           ImpParser
import           Text.Parsec
import           Text.Parsec.Language
import qualified Text.Parsec.Token    as Token
import           SMTMonad              ( SMT )
import qualified SMTMonad             as SMT
import           SMTParser
import           Spec

data OAQuery = OAQuery
             { oaSpecs       :: FunSpecMaps
             , oaPreCond     :: SMT.Expr
             , oaForallProgs :: [Prog]
             , oaExistsProgs :: [Prog]
             , oaPostCond    :: SMT.Expr
             }

data OAExec = OAForall String OAExecId | OAExists String OAExecId
type OAExecId = Maybe String
type NamedProg = (String, ParsedProg)

data OAExpectedResult = OASuccess | OAFailure
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

parseOrhleApp :: String -> Either ParseError ([OAExec], SMT OAQuery, OAExpectedResult)
parseOrhleApp str = runParser orhleAppParser () "" str

orhleAppParser :: OrhleAppParser ([OAExec], SMT OAQuery, OAExpectedResult)
orhleAppParser = do
  whiteSpace
  expectedResult <- try expectedValid <|> expectedInvalid; whiteSpace

  aExecs  <- option [] $ try $ execs "forall" OAForall; whiteSpace
  eExecs  <- option [] $ try $ execs "exists" OAExists; whiteSpace

  preCond <- option SMT.mkTrue $ do
    reserved "pre" >> whiteSpace >> char ':' >> whiteSpace
    condition
  whiteSpace
  postCond <- option SMT.mkTrue $ do
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
  let query = liftM5 OAQuery specs preCond (sequence aProgs) (sequence eProgs) postCond
  return $ ((aExecs ++ eExecs), query, expectedResult)

prefixProgram :: ParsedProg -> OAExec -> OrhleAppParser (SMT Prog)
prefixProgram prog exec = do
  case parseLoopSpecs prog of
        Left parseError -> error  $ show parseError
        Right z3Prog    -> return $ prefixProgVars (execPrefix exec) =<< z3Prog

execPrefix :: OAExec -> String
execPrefix exec = case (getExecId exec) of
                    Nothing  -> (getExecName exec) ++ "!"
                    Just eid -> (getExecName exec) ++ "!" ++ eid ++ "!"

untilSemi :: OrhleAppParser String
untilSemi = manyTill anyChar (try $ char ';')

condition :: OrhleAppParser (SMT SMT.Expr)
condition = do
  smtStr <- untilSemi
  whiteSpace
  case parseSMT smtStr of
    Left err  -> fail $ show err
    Right ast -> return ast

expectedValid :: OrhleAppParser OAExpectedResult
expectedValid = do
  reserved "expected" >> whiteSpace
  char ':' >> whiteSpace
  reserved "valid" >> whiteSpace
  semi >> whiteSpace
  return OASuccess

expectedInvalid :: OrhleAppParser OAExpectedResult
expectedInvalid = do
  reserved "expected" >> whiteSpace
  char ':' >> whiteSpace
  reserved "invalid" >> whiteSpace
  semi >> whiteSpace
  return OAFailure

execs :: String -> (String -> OAExecId -> OAExec) -> OrhleAppParser [OAExec]
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

specification :: OrhleAppParser (SMT ASTFunSpecMap)
specification = do
  name   <- identifier
  params <- (liftM concat) . parens $ sepBy varArray comma
  whiteSpace >> char '{' >> whiteSpace
  choiceVars <- option [] $ do
    reserved "choiceVars" >> whiteSpace >> char ':' >> whiteSpace
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
    return $ addFunSpec name (FunSpec params choiceVars pre post) emptyFunSpec

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

getExecName :: OAExec -> String
getExecName (OAForall name _) = name
getExecName (OAExists name _) = name

getExecId :: OAExec -> Maybe String
getExecId (OAForall _ eid) = eid
getExecId (OAExists _ eid) = eid

prefixProgVars :: String -> Prog -> SMT Prog
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
      pinv  <- SMT.prefixASTVars pre inv
      pvar  <- SMT.prefixASTVars pre var
      pbody <- prefixProgVars pre body
      return $ if local then SWhile (prefixB cond) pbody (pinv, pvar, local)
                        else SWhile (prefixB cond) pbody (inv,  pvar, local)
    SCall rets params fname -> return $ SCall (map prefix rets) (map prefix params) (prefix fname)
  where
    prefix s = pre ++ s
    prefixA = prefixAExpVars pre
    prefixB = prefixBExpVars pre
