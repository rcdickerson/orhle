{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.OrhleParser
  ( Exec(..)
  , ExecId
  , ExpectedResult(..)
  , OrhleParseResult(..)
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
import qualified Data.Set as Set
import Orhle.OrhleParserPrefix
import Orhle.SpecImp
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

data OrhleParseResult = OrhleParseResult { opr_execs    :: [Exec]
                                         , opr_impls    :: FunImplEnv SpecImpProgram
                                         , opr_specs    :: FunSpecEnv
                                         , opr_triple   :: RhleTriple
                                         , opr_expected :: ExpectedResult
                                         }

parseOrhle :: String -> Either ParseError OrhleParseResult
parseOrhle str = runParser orhleParser 0 "" str

orhleParser :: OrhleAppParser OrhleParseResult
orhleParser = do
  whiteSpace
  expectedResult <- option ExpectSuccess $
                    try expectedValid <|> expectedInvalid
  whiteSpace

  aExecs  <- option [] $ try $ execs "forall" ExecForall; whiteSpace
  eExecs  <- option [] $ try $ execs "exists" ExecExists; whiteSpace

  pre  <- option A.ATrue $ labeledAssertion "pre"
  post <- option A.ATrue $ labeledAssertion "post"

  aSpecs <- option Map.empty $ do
    reserved "aspecs" >> whiteSpace >> char ':' >> whiteSpace
    specs <- many $ try specification
    return $ Map.unions specs
  eSpecs <- option Map.empty $ do
    reserved "especs" >> whiteSpace >> char ':' >> whiteSpace
    specs <- many $ try specification
    return $ Map.unions specs

  -- TODO: better is to compose the parser combinators
  rest <- manyTill anyChar eof
  impls <- case parseFunImp rest of
    Left err   -> fail $ show err
    Right funs -> return $ Map.map funImplToSpecImp funs

  -- Add per-execution prefixed versions of each function implementation and
  -- specification to ensure names are unique across executions.
  let (aExecPrefixes, eExecPrefixes) = (map execPrefix aExecs, map execPrefix eExecs)
  let prefixedImpls   = Map.unions $ map (\eid -> prefixExecId eid impls) (aExecPrefixes ++ eExecPrefixes)
  let prefixedASpecs  = Map.unions $ map (\eid -> prefixExecId eid aSpecs) aExecPrefixes
  let prefixedESpecs  = Map.unions $ map (\eid -> prefixExecId eid eSpecs) eExecPrefixes

  aProgs <- mapM (lookupExecBody prefixedImpls) aExecs
  eProgs <- mapM (lookupExecBody prefixedImpls) eExecs
  return $ OrhleParseResult { opr_execs    = (aExecs ++ eExecs)
                            , opr_impls    = prefixedImpls
                            , opr_specs    = FunSpecEnv prefixedASpecs prefixedESpecs
                            , opr_triple   = RhleTriple pre aProgs eProgs post
                            , opr_expected = expectedResult
                            }

class ToSpecImp a where
  toSpecImp :: a -> SpecImpProgram
instance ToSpecImp (ImpSkip e) where
  toSpecImp _ = impSkip
instance ToSpecImp (ImpAsgn e) where
  toSpecImp (ImpAsgn lhs rhs) = impAsgn lhs rhs
instance ToSpecImp e => ToSpecImp (ImpSeq e) where
  toSpecImp (ImpSeq stmts) = impSeq $ map toSpecImp stmts
instance ToSpecImp e => ToSpecImp (ImpIf e) where
  toSpecImp (ImpIf c t e) = impIf c (toSpecImp t) (toSpecImp e)
instance ToSpecImp e => ToSpecImp (ImpWhile e) where
  toSpecImp (ImpWhile c body meta) = impWhileWithMeta c (toSpecImp body) meta
instance ToSpecImp e => ToSpecImp (ImpCall e) where
  toSpecImp (ImpCall cid args assignees) = specCall cid args assignees
instance (ToSpecImp (f e), ToSpecImp (g e)) => ToSpecImp ((f :+: g) e) where
  toSpecImp (Inl f) = toSpecImp f
  toSpecImp (Inr g) = toSpecImp g
instance ToSpecImp FunImpProgram where
  toSpecImp (In p) = toSpecImp p

funImplToSpecImp :: FunImpl FunImpProgram -> FunImpl SpecImpProgram
funImplToSpecImp (FunImpl params body returns) = FunImpl params (toSpecImp body) returns

lookupExecBody :: FunImplEnv SpecImpProgram -> Exec -> OrhleAppParser SpecImpProgram
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

specification :: OrhleAppParser SpecMap
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
  let spec = Specification params (getReturnVars post) choiceVars pre post
  return $ Map.fromList[ (callId, spec) ]

getReturnVars :: Assertion -> [Name]
getReturnVars assertion =
  let
    isRetName (Name n _) = n == "ret"
    assertionNames = Set.toList $ Name.namesIn assertion
  in filter isRetName assertionNames

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
