module Orhle
    ( AESpecs(..)
    , HlTriple(..)
    , HleTriple(..)
    , Exec(..)
    , ExecId
    , ExpectedResult(..)
    , Failure(..)
    , RhleTriple(..)
    , Spec(..)
    , SpecMap
    , Success(..)
    , addSpec
    , emptySpecMap
    , lookupSpec
    , parseOrhle
    , prefixSpecs
    , specAtCallsite
    , verify
    ) where

import Orhle.OrhleParser
import Orhle.Spec
import Orhle.Triple
import Orhle.Verifier

parseOrhle :: String -> Either String ([Exec], AESpecs, RhleTriple, ExpectedResult)
parseOrhle input = case parseOrhleApp input of
  Left err     -> Left  $ show err
  Right result -> Right $ result

verify :: AESpecs -> RhleTriple -> IO (Either Failure Success)
verify = rhleVerifier
