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
import Ceili.Evaluation
import Ceili.Language.AExpParser ( AExpParseable )
import Ceili.SMTString
import Ceili.StatePredicate
import Orhle.OrhleParser
import Orhle.SpecImp
import Orhle.Triple
import Orhle.Verifier
import Prettyprinter

parseOrhle :: ( Num t
              , AExpParseable t
              , AssertionParseable t
              ) => String -> Either String (OrhleParseResult t)
parseOrhle input = case Orhle.OrhleParser.parseOrhle input of
  Left err     -> Left  $ show err
  Right result -> Right $ result

verify :: ( Num t
          , Ord t
          , SMTString t
          , SMTTypeString t
          , AssertionParseable t
          , Pretty t
          , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (AExp t) t
          , Evaluable (SpecImpEvalContext t (SpecImpProgram t)) t (BExp t) Bool
          , StatePredicate (Assertion t) t
          ) => SpecImpEnv t (SpecImpProgram t) -> RhleTriple t -> IO (Either Failure Success)
verify = rhleVerifier
