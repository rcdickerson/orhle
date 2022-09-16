module Ceili.Language.FunImpParser
  ( ParseError
  , parseFunImp
  ) where

import Ceili.Assertion ( AssertionParseable )
import Ceili.Language.AExp
import Ceili.Language.AExpParser ( AExpParseable, parseAExp )
import Ceili.Language.FunImp
import qualified Ceili.Language.Imp as Imp
import qualified Ceili.Language.ImpParser as ImpParser
import Ceili.Name ( namesIn )
import qualified Ceili.Name as Name
import qualified Data.Map as Map
import Text.Parsec
import qualified Text.Parsec.Token as Token

type FunImpParser t a = Parsec String (FunImplEnv (FunImpProgram t)) a
type ProgramParser t = FunImpParser t (FunImpProgram t)

funImpLanguageDef :: Token.LanguageDef a
funImpLanguageDef = ImpParser.impLanguageDef {
    Token.reservedNames = Token.reservedNames ImpParser.impLanguageDef
                       ++ ["fun", "return"]
  }

lexer      = Token.makeTokenParser funImpLanguageDef
braces     = Token.braces     lexer
comma      = Token.comma      lexer
identifier = Token.identifier lexer
integer    = Token.integer    lexer
parens     = Token.parens     lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
semi       = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer

parseFunImp :: ( Num t
               , AExpParseable t
               , AssertionParseable t)
            => String -> Either ParseError (FunImplEnv (FunImpProgram t))
parseFunImp str = runParser program Map.empty "" str

program :: ( Num t
           , AExpParseable t
           , AssertionParseable t )
        => FunImpParser t (FunImplEnv (FunImpProgram t))
program = do
  _ <- many1 $ whiteSpace >> funDef
  getState

statement :: (AExpParseable t, AssertionParseable t) => ProgramParser t
statement = try funCall
        <|> ImpParser.parseIf lexer statement
        <|> ImpParser.parseWhile lexer statement
        <|> ImpParser.parseSkip lexer
        <|> ImpParser.parseAsgn lexer
        <|> parens statement

funDef :: (Num t, AExpParseable t, AssertionParseable t) => FunImpParser t ()
funDef = do
  reserved "fun"
  handle <- identifier
  params <- nameTuple
  (body, rets) <- braces (funBody handle)
  recordFunDef handle params body rets

funBody :: (Num t, AExpParseable t, AssertionParseable t)
        => Name.Handle -> FunImpParser t ((FunImpProgram t), [Name])
funBody cid = do
  bodyStmts <- many statement
  retExprs  <- option [ALit 0] returnStatement
  let freshIds = Name.buildFreshIds $ namesIn (Imp.ImpSeq bodyStmts)
      retVal   = Name (cid ++ "!retVal") 0
      retNames = snd $ foldr (\_ (ids, names) ->
                                 let (ids', nextFresh) = Name.runFreshen ids retVal
                                 in  (ids', nextFresh:names))
                       (freshIds, [])
                       retExprs
      asgns    = map (uncurry Imp.impAsgn) $ zip retNames retExprs
      body     = bodyStmts ++ asgns
  return (Imp.impSeq body, retNames)

returnStatement :: AExpParseable t => FunImpParser t [AExp t]
returnStatement = do
  reserved "return"
  retExprs <- try varArrayOrAExp
          <|> aexpTuple
  _ <- semi
  return retExprs

funCall :: AExpParseable t => ProgramParser t
funCall = do
  assignees <- (try nameTuple) <|> nameArrayOrName
  reservedOp ":="
  funName <- identifier
  args    <- aexpTuple
  _ <- semi
  return $ impCall funName args assignees

nameTuple :: FunImpParser t [Name]
nameTuple = do
  names <- parens $ sepBy nameArrayOrName comma
  return $ concat names

nameArray :: FunImpParser t [Name]
nameArray = do
  var <- name
  char '[' >> whiteSpace
  num <- integer
  char ']' >> whiteSpace
  return $ case num of
    0 -> [ var ]
    _ -> let (Name vname i) = var
         in map (\n -> Name (vname ++ "_" ++ (show n)) i) [0..(num-1)]

nameArrayOrName :: FunImpParser t [Name]
nameArrayOrName = (try nameArray) <|> (do n <- name; return [n])

varArray :: FunImpParser t [AExp t]
varArray = do
  names <- nameArray
  return $ map AVar names

aexpTuple :: AExpParseable t => FunImpParser t [AExp t]
aexpTuple = do
  args <- parens $ sepBy varArrayOrAExp comma
  return $ concat args

varArrayOrAExp :: AExpParseable t => FunImpParser t [AExp t]
varArrayOrAExp = (try varArray) <|> (do aexp <- parseAExp; return [aexp])

name :: FunImpParser t Name
name = identifier >>= (return . Name.fromString)

recordFunDef :: Name.Handle
             -> [Name]
             -> FunImpProgram t
             -> [Name]
             -> FunImpParser t ()
recordFunDef handle params body rets = do
  funs <- getState
  putState $ Map.insert handle (FunImpl params body rets) funs
  return ()
