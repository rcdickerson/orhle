module Orhle
    ( HlTriple(..)
    , HleTriple(..)
    , Exec(..)
    , ExecId
    , ExpectedResult(..)
    , Failure(..)
    , FunImpl(..)
    , FunImplEnv
    , Name(..)
    , OrhleParseResult(..)
    , SpecImpEnv(..)
    , TypedName(..)
    , Type(..)
    , RhleTriple(..)
    , SpecMap
    , Success(..)
    , Orhle.parseOrhle
    , verify
    ) where

import Ceili.Name
import Orhle.OrhleParser
import Orhle.SpecImp
import Orhle.Triple
import Orhle.Verifier

parseOrhle :: String -> Either String OrhleParseResult
parseOrhle input = case Orhle.OrhleParser.parseOrhle input of
  Left err     -> Left  $ show err
  Right result -> Right $ result

verify :: SpecImpEnv SpecImpProgram -> RhleTriple -> IO (Either Failure Success)
verify = rhleVerifier
