module Orhle
    ( AESpecs(..)
    , HlTriple(..)
    , HleTriple(..)
    , Exec(..)
    , ExecId
    , ExpectedResult(..)
    , Failure(..)
    , FunImplEnv
    , Name(..)
    , RhleTriple(..)
    , Spec(..)
    , SpecMap
    , Success(..)
    , addSpec
    , emptySpecMap
    , lookupSpec
    , Orhle.parseOrhle
    , prefixSpecs
    , specAtCallsite
    , verify
    ) where

import Orhle.Imp
import Orhle.OrhleParser
import Orhle.Spec
import Orhle.Triple
import Orhle.Verifier

parseOrhle :: String -> Either String ([Exec], FunImplEnv, AESpecs, RhleTriple, ExpectedResult)
parseOrhle input = case Orhle.OrhleParser.parseOrhle input of
  Left err     -> Left  $ show err
  Right result -> Right $ result

verify :: AESpecs -> RhleTriple -> IO (Either Failure Success)
verify = rhleVerifier
