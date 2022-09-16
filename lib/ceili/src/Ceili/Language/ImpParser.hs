{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Ceili.Language.ImpParser
  ( ParseError
  , ProgramParser
  , impLanguageDef
  , parseAsgn
  , parseIf
  , parseImp
  , parseSkip
  , parseWhile
  ) where

import Ceili.Assertion
import Ceili.Language.AExpParser ( AExpParseable, parseAExp )
import Ceili.Language.BExpParser ( parseBExp )
import Ceili.Language.Compose
import Ceili.Language.Imp
import qualified Ceili.Name as Name
import Text.Parsec
import Text.Parsec.Token ( TokenParser )
import qualified Text.Parsec.Token as Token

impLanguageDef :: Token.LanguageDef s
impLanguageDef = Token.LanguageDef
  { Token.caseSensitive   = True
  , Token.commentStart    = "/*"
  , Token.commentEnd      = "*/"
  , Token.commentLine     = "//"
  , Token.identStart      = letter <|> char '@'
  , Token.identLetter     = alphaNum <|> char '_' <|> char '!'
  , Token.nestedComments  = True
  , Token.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Token.reservedNames   = [ "if", "then", "else", "endif"
                            , "while", "do", "end"
                            , "@inv", "@var"
                            , "skip"
                            , "true", "false"
                            ]
  , Token.reservedOpNames = [":="]
  }

type ImpParser s a     = Parsec String s a
type ProgramParser s t = ImpParser s (ImpProgram t)

parseImp :: ( AExpParseable t
            , AssertionParseable t )
         => String
         -> Either ParseError (ImpProgram t)
parseImp str = runParser impProgram () "" str

impProgram :: ( AExpParseable t
              , AssertionParseable t )
           => ProgramParser s t
impProgram = do
  let impLexer = Token.makeTokenParser $ impLanguageDef
  stmts <- many1 $ (Token.whiteSpace impLexer >> statement impLexer)
  return $ impSeqIfNeeded stmts

type BasicImpProg t f = ( ImpAsgn t  :<: f
                        , ImpIf t    :<: f
                        , ImpSeq t   :<: f
                        , ImpSkip t  :<: f
                        , ImpWhile t :<: f
                        )

statement :: ( AExpParseable t
             , AssertionParseable t
             , BasicImpProg t f )
          => TokenParser s
          -> ImpParser s (ImpExpr t f)
statement lexer = (Token.parens lexer $ statement lexer)
              <|> parseIf lexer (statement lexer)
              <|> parseWhile lexer (statement lexer)
              <|> parseSkip lexer
              <|> parseAsgn lexer

parseSkip :: ImpSkip t :<: f => TokenParser s -> ImpParser s (ImpExpr t f)
parseSkip lexer = do
  Token.reserved lexer "skip"
  _ <- Token.semi lexer
  return $ impSkip

parseAsgn :: ( AExpParseable t
             , ImpAsgn t :<: f )
          => TokenParser s
          -> ImpParser s (ImpExpr t f)
parseAsgn lexer = do
  var <- name lexer
  Token.reservedOp lexer ":="
  expr <- parseAExp
  _ <- Token.semi lexer
  return $ impAsgn var expr

parseIf :: ( AExpParseable t
           , AssertionParseable t
           , BasicImpProg t f )
        => TokenParser s
        -> ImpParser s (ImpExpr t f)
        -> ImpParser s (ImpExpr t f)
parseIf lexer stmtParser = do
  Token.reserved lexer "if"
  cond  <- parseBExp
  Token.reserved lexer "then"
  tbranch <- many1 $ stmtParser
  ebranch <- option [] $
    (Token.reserved lexer "else" >>= \_ -> many1 $ statement lexer)
  Token.reserved lexer "endif"
  return $ impIf cond (impSeqIfNeeded tbranch) (impSeqIfNeeded ebranch)

parseWhile :: ( AExpParseable t
              , AssertionParseable t
              , BasicImpProg t f )
           => TokenParser s
           -> ImpParser s (ImpExpr t f)
           -> ImpParser s (ImpExpr t f)
parseWhile lexer stmtParser = do
  Token.reserved lexer "while"
  cond  <- parseBExp
  Token.whiteSpace lexer
  Token.reserved lexer "do"
  inv <- option Nothing $ do
    Token.reserved lexer "@inv"
    invStr <- Token.braces lexer $ many $ noneOf "{}"
    case parseAssertion invStr of
      Left err  -> fail (show err)
      Right inv -> return $ Just inv
  var <- option Nothing $ do
    Token.reserved lexer "@var"
    varStr <- Token.braces lexer $ many $ noneOf "{}"
    case parseArith varStr of
      Left err  -> fail (show err)
      Right var -> return $ Just var
  Token.whiteSpace lexer
  body  <- many1 $ try stmtParser
  Token.whiteSpace lexer
  Token.reserved lexer "end"
  let meta = ImpWhileMetadata Nothing inv var
  return $ impWhileWithMeta cond (impSeqIfNeeded body) meta

name :: TokenParser s -> ImpParser s Name
name lexer = Token.identifier lexer >>= (return . Name.fromString)
