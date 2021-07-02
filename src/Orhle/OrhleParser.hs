{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.OrhleParser
  ( Exec(..)
  , ExecId
  , ExpectedResult(..)
  , parseOrhle
  ) where

import Ceili.Assertion ( Assertion(..) )
import qualified Ceili.Assertion as A
import Ceili.Language.Compose ( (:+:)(..) )
import Ceili.Language.FunImp
import Ceili.Language.FunImpParser
import Ceili.Name ( Name(..), TypedName(..) )
import qualified Ceili.Name as Name
import Control.Monad ( liftM )
import qualified Data.Map as Map
import Orhle.Spec ( Spec(..) )
import qualified Orhle.Spec as S
import Orhle.Triple
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

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

parseOrhle :: String -> Either ParseError ([Exec], FunImplEnv, S.AESpecs, RhleTriple, ExpectedResult)
parseOrhle str = runParser orhleParser 0 "" str

orhleParser :: OrhleAppParser ([Exec], FunImplEnv, S.AESpecs, RhleTriple, ExpectedResult)
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

  -- TODO: better is to compose the parser combinators
  rest <- manyTill anyChar eof
  impls <- case parseFunImp rest of
    Left err   -> fail $ show err
    Right funs -> return funs

  -- Add per-execution prefixed versions of each function implementation to
  -- ensure names are unique across executions. This keeps the verifier from
  -- needing to worry about polluting cross-execution namespaces when
  -- constructing relational verification conditions, and ensures prefixed call
  -- names in each program have appropriate entries in the implementation
  -- environment.
  let execPrefixes         = map execPrefix (aExecs ++ eExecs)
  let allPrefixes key impl = map (\p -> (p ++ key, prefixImpl p impl)) execPrefixes
  let prefixedAssocs       = concat $ map (uncurry allPrefixes) (Map.assocs impls)
  let impls'               = Map.fromList prefixedAssocs

  -- Similarly, prefix the specifications.
  let prefixExecId specMap exec = S.prefixSpecs (execPrefix exec) specMap
  let prefixedASpecs = Map.unions $ map (prefixExecId aSpecs) aExecs
  let prefixedESpecs = Map.unions $ map (prefixExecId eSpecs) eExecs
  let specs = S.AESpecs prefixedASpecs prefixedESpecs

  aProgs <- mapM (lookupExecBody impls') aExecs
  eProgs <- mapM (lookupExecBody impls') eExecs
  return $ ((aExecs ++ eExecs)
           , impls'
           , specs
           , RhleTriple pre aProgs eProgs post
           , expectedResult)

prefixImpl :: String -> FunImpl -> FunImpl
prefixImpl prefix (FunImpl params body rets) = let
  pParams   = map (Name.prefix prefix) params
  pBody     = (Name.prefix prefix) . (prefixCallIds prefix) $ body
  pRets     = map (Name.prefix prefix) rets
  in FunImpl pParams pBody pRets

class CallIdPrefixer a where
  prefixCallIds :: String -> a -> a
instance CallIdPrefixer (ImpSkip e) where
  prefixCallIds _ = id
instance CallIdPrefixer (ImpAsgn e) where
  prefixCallIds _ = id
instance CallIdPrefixer e => CallIdPrefixer (ImpSeq e) where
  prefixCallIds pre (ImpSeq stmts) = ImpSeq $ map (prefixCallIds pre) stmts
instance CallIdPrefixer e => CallIdPrefixer (ImpIf e) where
  prefixCallIds pre (ImpIf c t e) = ImpIf c (prefixCallIds pre t) (prefixCallIds pre t)
instance CallIdPrefixer e => CallIdPrefixer (ImpWhile e) where
  prefixCallIds pre (ImpWhile c body meta) = ImpWhile c (prefixCallIds pre body) meta
instance CallIdPrefixer e => CallIdPrefixer (ImpCall e) where
  prefixCallIds pre (ImpCall cid params asgns) = ImpCall (pre ++ cid) params asgns
instance (CallIdPrefixer (f e), CallIdPrefixer (g e)) => CallIdPrefixer ((f :+: g) e) where
  prefixCallIds pre (Inl f) = Inl $ prefixCallIds pre f
  prefixCallIds pre (Inr g) = Inr $ prefixCallIds pre g
instance CallIdPrefixer FunImpProgram where
  prefixCallIds pre (In f) = In $ prefixCallIds pre f

lookupExecBody :: FunImplEnv -> Exec -> OrhleAppParser FunImpProgram
lookupExecBody funs exec =
  let
    name = (execPrefix exec) ++ (getExecName exec)
  in case Map.lookup name funs of
    Nothing   -> fail   $ "Function definition not found: " ++ name
    Just impl -> return $ fimpl_body impl

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
  callId <- identifier
  params <- (liftM concat) . parens $ sepBy varArray comma
  whiteSpace >> char '{' >> whiteSpace
  choiceVars <- option [] $ do
    reserved "choiceVars" >> whiteSpace >> char ':' >> whiteSpace
    vars <- sepBy name comma
    whiteSpace >> char ';' >> whiteSpace
    return $ map (\n -> TypedName n Name.Int) vars
  pre  <- option A.ATrue $ labeledAssertion "pre"
  post <- option A.ATrue $ labeledAssertion "post"
  whiteSpace >> char '}' >> whiteSpace
  let spec = Spec params choiceVars pre post
  return $ S.addSpec callId spec S.emptySpecMap

name :: OrhleAppParser Name
name = identifier >>= (return . Name.fromString)

labeledAssertion :: String -> OrhleAppParser Assertion
labeledAssertion label = do
  reserved label >> whiteSpace >> char ':' >> whiteSpace
  str <- untilSemi
  whiteSpace
  case A.parseAssertion str of
    Left error      -> fail $ show error
    Right assertion -> return assertion

varArray :: OrhleAppParser [Name]
varArray = do
  (Name vname i, num) <- try (do
                                 var <- name
                                 char '[' >> whiteSpace
                                 num <- integer
                                 char ']' >> whiteSpace
                                 return (var, num))
                         <|> (do var <- name; return (var, 0))
  return $ if (num == 0)
             then [Name vname i]
             else map (\n -> Name (vname ++ "_" ++ (show n)) i) [0..(num-1)]

getExecName :: Exec -> String
getExecName (ExecForall name _) = name
getExecName (ExecExists name _) = name

getExecId :: Exec -> Maybe String
getExecId (ExecForall _ eid) = eid
getExecId (ExecExists _ eid) = eid
