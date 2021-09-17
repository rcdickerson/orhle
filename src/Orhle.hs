{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}

module Orhle
  ( HlTriple(..)
  , HleTriple(..)
  , Exec(..)
  , ExecId
  , ExpectedResult(..)
  , Failure(..)
  , FunImpl(..)
  , FunImplEnv
  , FunSpecEnv(..)
  , Name(..)
  , OrhleParseResult(..)
  , SMTString(..)
  , SMTTypeString(..)
  , SpecImpEnv(..)
  , RhleTriple(..)
  , SpecMap
  , Success(..)
  , Orhle.parseOrhle
  , showSMT
  , verify
  ) where

import Ceili.Assertion
import Ceili.Language.AExpParser ( AExpParseable )
import Ceili.SMTString
import Orhle.OrhleParser
import Orhle.SpecImp
import Orhle.Triple
import Orhle.Verifier

parseOrhle :: ( Num t
              , AExpParseable t
              , AssertionParseable t
              ) => String -> Either String (OrhleParseResult t)
parseOrhle input = case Orhle.OrhleParser.parseOrhle input of
  Left err     -> Left  $ show err
  Right result -> Right $ result

verify :: SpecImpEnv Integer (SpecImpProgram Integer)
       -> RhleTriple Integer
       -> IO (Either Failure Success)
verify = rhleVerifier
