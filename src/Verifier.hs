module Verifier
  ( Verifier
  , VResult
  , VTracedResult
  , runVerifier
  ) where

import Control.Monad.Writer
import Data.List(intercalate)
import qualified Data.Map as Map
import Imp
import InterpMap
import VTrace
import RHLE
import Z3.Monad

type Verifier = RHLETrip -> Z3 (VResult, [VTrace])
type VResult       = Either String InterpMap
type VTracedResult = WriterT [VTrace] Z3 VResult

runVerifier :: Verifier -> String -> Prog -> Prog -> String -> IO String
runVerifier verifier pre progA progE post = do
  (_, result) <- evalZ3 $ runWriterT $ runVerifier' verifier pre progA progE post
  return result

runVerifier' :: Verifier -> String -> Prog -> Prog -> String -> WriterT String Z3 ()
runVerifier' verifier pre progA progE post = do
  tell "------------------------------------------------\n"
  tell $ "Universal Program:\n" ++ (show progA) ++     "\n"
  tell "------------------------------------------------\n"
  tell $ "Existential Program:\n" ++ (show progE) ++   "\n"
  tell "------------------------------------------------\n"
  trip <- lift $ mkRHLETrip pre progA progE post
  (result, trace) <- lift $ verifier trip
  traceStr <- lift $ ppVTrace trace
  tell $ "Verification Trace:\n" ++ traceStr ++ "\n"
  tell "------------------------------------------------\n"
  case result of
    Right interp -> do
      tell "VALID iff the following executions are possible:\n"
      let funNames = assigneeToFuncNames (Seq [progA, progE])
      let funMap   = Map.mapKeys (\v -> Map.findWithDefault v v funNames) interp
      mapLines <- lift $ ppInterpMap funMap
      tell $ intercalate "\n" mapLines
      tell $ "\n"
    Left reason -> do
      tell $ "INVALID: " ++ reason ++ "\n"
  tell "------------------------------------------------"

assigneeToFuncNames :: Prog -> Map.Map Var String
assigneeToFuncNames prog =
  case prog of
    Seq s      -> Map.unions $ map assigneeToFuncNames s
    If _ s1 s2 -> Map.unions $ map assigneeToFuncNames [s1, s2]
    Call v (UFunc name _ _ _)
               -> Map.singleton v name
    _          -> Map.empty
