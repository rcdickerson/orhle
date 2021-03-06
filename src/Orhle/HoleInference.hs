module Orhle.HoleInference
  ( InferenceStrategy(..)
  , inferAndCheck
  ) where

import Debug.Trace

import           Control.Monad ( foldM )
import           Data.Map  ( Map )
import qualified Data.Map as Map
import           Data.Set  ( Set )
import qualified Data.Set as Set
import           Orhle.Assertion ( Arith(..)
                                 , Assertion(..)
                                 , Ident(..) )
import qualified Orhle.Assertion as A
import qualified Orhle.SMT as SMT

data InferenceStrategy = DisallowHoles
                       | Enumerative { maxDepth :: Int }
                       -- | Abductive

type ErrorMsg = String

inferAndCheck :: InferenceStrategy -> Assertion -> IO (Either ErrorMsg Assertion)
inferAndCheck strategy assertion =
  if countHoles assertion == 0 then check assertion else
  case strategy of
    DisallowHoles        -> return $ Left "Inferring missing assertions is not supported"
    Enumerative maxDepth -> enumerativeSynth maxDepth assertion

countHoles :: Assertion -> Int
countHoles assertion = case assertion of
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
  Hole _     -> 1
  where
    sumHoles = sum . (map countHoles)

intVarsAtHoles :: Assertion -> Map Int (Set Ident)
intVarsAtHoles assertion =
  let varScope inScope assertion =
        case assertion of
          ATrue        -> Map.empty
          AFalse       -> Map.empty
          Atom _       -> Map.empty
          Not  a       -> varScope inScope a
          And  as      -> Map.unions $ map (varScope inScope) as
          Or   as      -> Map.unions $ map (varScope inScope) as
          Imp  a1 a2   -> Map.union (varScope inScope a1) (varScope inScope a2)
          Eq   _ _     -> Map.empty
          Lt   _ _     -> Map.empty
          Gt   _ _     -> Map.empty
          Lte  _ _     -> Map.empty
          Gte  _ _     -> Map.empty
          Forall ids a -> varScope (Set.union inScope $ Set.fromList ids) a
          Exists ids a -> varScope (Set.union inScope $ Set.fromList ids) a
          Hole i       -> Map.singleton i inScope
  in varScope (Set.filter ((== A.Int). identSort) $ A.freeVars assertion) assertion

enumerativeSynth :: Int -> Assertion -> IO (Either ErrorMsg Assertion)
enumerativeSynth maxDepth assertion = let
  vars = Map.map Set.toList $ intVarsAtHoles assertion
  assertions = Map.map (enumerateAssertions maxDepth) vars
  in do
    traceM $ "Assertion: " ++ (show assertion)
    traceM $ "Free vars: " ++ (show vars)
    --traceM $ "Assertions: " ++ (show assertions)
    return $ Left ""
    -- traceM $ "Assertion length: " ++ (show $ length assertions)
    -- traceM $ "Assertions: " ++ (show assertions)
    -- result <- foldM (\result assertion -> case result of
    --                     Right a -> return $ Right a
    --                     Left _  -> check assertion) (Left "") assertions
    -- case result of
    --   Right a -> return $ Right a
    --   Left _  -> return $ Left "Unable to synthesize fills for assertion holes."

enumerateAssertions :: Int -> [Ident] -> [Assertion]
enumerateAssertions 0 _ = [ ATrue, AFalse ]
enumerateAssertions depth ids = let
  prevAssert = enumerateAssertions (depth - 1) ids
  prevArith  = enumerateAriths     (depth - 1) ids
  (commAssert, nonCommAssert) = computeOperands prevAssert
  (commArith,  nonCommArith)  = computeOperands prevArith
  in prevAssert ++
     (map Not prevAssert) ++
     (map And $ unpairs commAssert) ++
     (map Or  $ unpairs commAssert) ++
     (map (uncurry Imp) nonCommAssert) ++
     (map (uncurry Eq) commArith) ++
     (map (uncurry Lt) nonCommArith) ++
     (map (uncurry Gt) nonCommArith)

enumerateAriths :: Int -> [Ident] -> [Arith]
enumerateAriths 0 ids     = map A.Var ids
enumerateAriths depth ids = let
  prevDepth = enumerateAriths (depth - 1) ids
  (comm, nonComm) = computeOperands prevDepth
  in prevDepth ++
     (map A.Add $ unpairs comm) ++
     (map A.Sub $ unpairs nonComm) ++
     (map A.Mul $ unpairs comm) ++
     (map (uncurry A.Div) nonComm) ++
     (map (uncurry A.Mod) nonComm)

computeOperands :: [a] -> ([(a, a)], [(a, a)])
computeOperands as = let
  comm    = pairs as
  nonComm = comm ++ (pairs $ reverse as)
  in (comm, nonComm)

pairs :: [a] -> [(a, a)]
pairs []       = []
pairs (x:rest) = [(x, y) | y <- rest] ++ (pairs rest)

unpairs :: [(a, a)] -> [[a]]
unpairs = map (\(x, y) -> [x, y])

check :: Assertion -> IO (Either ErrorMsg Assertion)
check assertion = do
  result <- SMT.checkValid assertion
  case result of
    SMT.Sat m   -> return . Left  $ m
    SMT.Unsat   -> return . Right $ assertion
    SMT.Unknown -> return . Left  $ ":: solver returned unknown ::"
