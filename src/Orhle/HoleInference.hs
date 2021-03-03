module Orhle.HoleInference
  ( InferenceStrategy(..)
  , inferAndCheck
  ) where

import Orhle.Assertion ( Assertion(..) )
import qualified Orhle.SMT as SMT

data InferenceStrategy = DisallowHoles
                       -- | Enumerative { maxDepth :: Int }
                       -- | Abductive

type ErrorMsg = String

inferAndCheck :: InferenceStrategy -> Assertion -> IO (Either ErrorMsg Assertion)
inferAndCheck strategy assertion = let
  holeCount = countHoles assertion
  in case strategy of
    DisallowHoles -> if holeCount == 0
                     then check assertion
                     else return $ Left "Inferring missing assertions is not supported"

countHoles :: Assertion -> Int
countHoles assertion = let
  sumHoles = sum . (map countHoles)
  in case assertion of
    ATrue      -> 0
    AFalse     -> 0
    Atom _     -> 0
    Not a      -> countHoles a
    And as     -> sumHoles as
    Or  as     -> sumHoles as
    Imp a1 a2  -> sumHoles [a1, a2]
    Eq  _ _    -> 0
    Lt  _ _    -> 0
    Gt  _ _    -> 0
    Lte _ _    -> 0
    Gte _ _    -> 0
    Forall _ a -> countHoles a
    Exists _ a -> countHoles a
    Hole       -> 1

check :: Assertion -> IO (Either ErrorMsg Assertion)
check assertion = do
  result <- SMT.checkValid assertion
  case result of
    SMT.Sat m   -> return . Left  $ m
    SMT.Unsat   -> return . Right $ assertion
    SMT.Unknown -> return . Left  $ ":: solver returned unknown ::"
