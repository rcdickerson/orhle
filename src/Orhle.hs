module Orhle
    ( AESpecs(..)
    , HlTriple(..)
    , HleTriple(..)
    , Exec(..)
    , ExecId
    , ExpectedResult(..)
    , Failure(..)
    , FunImpl(..)
    , FunImplEnv
    , Name(..)
    , RhleTriple(..)
    , Spec(..)
    , SpecMap
    , Success(..)
    , addSpec
    , emptySpecMap
    , inline
    , lookupSpec
    , Orhle.parseOrhle
    , prefixSpecs
    , verify
    ) where

import Orhle.Imp
import Orhle.Inliner
import Orhle.OrhleParser
import Orhle.Spec
import Orhle.Triple
import Orhle.Verifier

parseOrhle :: String -> Either String ([Exec], FunImplEnv, AESpecs, RhleTriple, ExpectedResult)
parseOrhle input = case Orhle.OrhleParser.parseOrhle input of
  Left err     -> Left  $ show err
  Right result -> Right $ result

verify :: AESpecs -> FunImplEnv -> RhleTriple -> IO (Either Failure Success)
verify = rhleVerifier
