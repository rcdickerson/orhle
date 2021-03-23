module Orhle.InvariantInference
  ( ErrorMsg
  , InferenceStrategy(..)
  , ValsAtHole
  , VCTransform
  , inferAndCheck
  ) where

import System.IO
import Control.Concurrent.Timeout

import           Data.Map  ( Map, (!) )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Orhle.Assertion ( Arith(..)
                                 , Assertion(..) )
import qualified Orhle.Assertion as A
import qualified Orhle.Imp as Imp
import qualified Orhle.SMT as SMT

type ErrorMsg          = String
data InferenceStrategy = DisallowHoles
                       | Enumerative { maxDepth :: Int }
type ValsAtHole        = Int -> [Arith]
type VCTransform       = [Imp.Program] -> [Imp.Program] -> Assertion

inferAndCheck :: InferenceStrategy -> ValsAtHole -> VCTransform
              -> [Imp.Program] -> [Imp.Program]
              -> IO (Either ErrorMsg (Map Int Assertion))
inferAndCheck strategy varsAtHole vcTransform aProgs eProgs =
  if countInvariantHoles (aProgs ++ eProgs) == 0
  then do
    result <- check (vcTransform aProgs eProgs)
    return $ case result of
      Left msg -> Left msg
      Right _  -> Right Map.empty
  else case strategy of
    DisallowHoles     -> return $ Left "Inferring missing assertions is not supported"
    Enumerative depth -> enumerativeSynth depth varsAtHole vcTransform aProgs eProgs

countInvariantHoles :: [Imp.Program] -> Int
countInvariantHoles = length . Set.toList . Set.unions . (map invHoleIds)

countAssertionHoles :: Assertion -> Int
countAssertionHoles assertion = case assertion of
  ATrue      -> 0
  AFalse     -> 0
  Atom _     -> 0
  Not a      -> countAssertionHoles a
  And as     -> sumHoles as
  Or  as     -> sumHoles as
  Imp a1 a2  -> sumHoles [a1, a2]
  Eq  _ _    -> 0
  Lt  _ _    -> 0
  Gt  _ _    -> 0
  Lte _ _    -> 0
  Gte _ _    -> 0
  Forall _ a -> countAssertionHoles a
  Exists _ a -> countAssertionHoles a
  Hole _     -> 1
  where
    sumHoles = sum . (map countAssertionHoles)

invHoleIds :: Imp.Program -> Set.Set Int
invHoleIds prog = case prog of
  Imp.SSkip                  -> Set.empty
  Imp.SAsgn _ _              -> Set.empty
  Imp.SSeq ps                -> Set.unions $ map invHoleIds ps
  Imp.SIf _ p1 p2            -> Set.union (invHoleIds p1) (invHoleIds p2)
  Imp.SCall _ _ _            -> Set.empty
  Imp.SWhile _ body (inv, _) -> Set.union (invHoleIds body) $
      case inv of
        A.Hole hid -> Set.singleton hid
        _          -> Set.empty

fillInvHole :: Imp.Program -> Int -> Assertion -> Imp.Program
fillInvHole prog holeId fill = let
  fillRec p = fillInvHole p holeId fill
  in case prog of
    Imp.SSkip                    -> Imp.SSkip
    asgn@(Imp.SAsgn _ _)         -> asgn
    Imp.SSeq ps                  -> Imp.SSeq $ map fillRec ps
    Imp.SIf c p1 p2              -> Imp.SIf c (fillRec p1) (fillRec p2)
    call@(Imp.SCall _ _ _)       -> call
    Imp.SWhile c body (inv, var) ->
      let inv' = case inv of
            A.Hole hid -> if hid == holeId then fill else inv
            _          -> inv
      in Imp.SWhile c (fillRec body) (inv', var)

enumerativeSynth :: Int -> ValsAtHole -> VCTransform
                 -> [Imp.Program] -> [Imp.Program]
                 -> IO (Either ErrorMsg (Map Int Assertion))
enumerativeSynth depth valsAtHole vcTransform aProgs eProgs =
  let
    holeIds  = Set.unions $ map invHoleIds (aProgs ++ eProgs)
    holeVals = Map.fromSet valsAtHole holeIds
  in do
    putStrLn $ "Var map: " ++ (show holeVals)
    putStrLn $ "Fills: " ++ (show . length $ (enumerateAssertions depth $ holeVals!0))
    result <- tryAllFills depth holeVals Map.empty vcTransform aProgs eProgs
    case result of
      Left msg -> putStrLn msg -- TODO: Logger
      Right a  -> putStrLn $ "Found fills: " ++ (show a) -- TODO : Logger
    return result

tryAllFills :: Int -> (Map Int [Arith]) -> (Map Int Assertion) -> VCTransform
            -> [Imp.Program] -> [Imp.Program]
            -> IO (Either ErrorMsg (Map Int Assertion))
tryAllFills depth holeVals currentSubs vcTransform aProgs eProgs =
  if Map.null holeVals
  then do
    result <- timeout (100000 * 20) $ check (vcTransform aProgs eProgs)
    case result of
      Nothing -> putStr "_"
      Just (Left _) -> putStr "."
      Just (Right _) -> putStr "|"
    hFlush stdout
    return $ case result of
      Nothing         -> Left "timeout"
      Just (Left msg) -> Left msg
      Just (Right _ ) -> Right currentSubs
  else let
    holeId               = head $ Map.keys holeVals
    fills                = enumerateAssertions depth $ holeVals!holeId
    holeVals'            = Map.delete holeId holeVals
    fillProgs progs fill = map (\prog -> fillInvHole prog holeId fill) progs
    subsAndFills fill    = ( Map.insert holeId fill currentSubs
                           , fillProgs aProgs fill
                           , fillProgs eProgs fill )
    filledProgs          = map subsAndFills fills
    tryFill (subs, filledAProgs, filledEProgs)
                         = tryAllFills depth holeVals' subs vcTransform filledAProgs filledEProgs
    in firstRight $ map tryFill filledProgs

firstRight :: [IO (Either ErrorMsg (Map Int Assertion))] -> IO (Either ErrorMsg (Map Int Assertion))
firstRight []         = return $ Left "Unable to find fills for assertion holes."
firstRight (try:rest) = do
  result <- try
  case result of
    Left _  -> firstRight rest
    Right a -> return $ Right a

enumerateAssertions :: Int -> [Arith] -> [Assertion]
enumerateAssertions 0 _ = []
enumerateAssertions depth vars = let
  prevAssert = enumerateAssertions (depth - 1) vars
  prevArith  = enumerateAriths     (depth - 1) vars
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

enumerateAriths :: Int -> [Arith] -> [Arith]
enumerateAriths 0 vars    = vars
enumerateAriths depth ids = let
  prevDepth = enumerateAriths (depth - 1) ids
  (comm, nonComm) = computeOperands prevDepth
  in prevDepth ++
     (map A.Add $ unpairs comm) ++
     (map A.Sub $ unpairs nonComm) ++
     (map A.Mul $ unpairs comm) -- ++
--     (map (uncurry A.Div) nonComm) ++
--     (map (uncurry A.Mod) nonComm)

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

check :: Assertion -> IO (Either ErrorMsg ())
check assertion =
  if countAssertionHoles assertion > 0
  then return $ Left "VCs contain holes even when all invariants are supplied"
  else do
    result <- SMT.checkValid assertion
    return $ case result of
      SMT.Valid         -> Right ()
      SMT.Invalid model -> Left  model
      SMT.ValidUnknown  -> Left  "Solver returned unknown"
