module Main where

import Lib
import qualified Data.Map as Map
import Z3.Monad

main :: IO ()
main = useVerifier2

useVerifier1 :: IO ()
useVerifier1 = do
  putStrLn "------------------------------------------------"
  putStrLn $ "Universal Program:\n" ++ (show.rhleProgA $ rhleTrip)
  putStrLn "------------------------------------------------"
  putStrLn $ "Existential Program:\n" ++ (show.rhleProgE $ rhleTrip)
  putStrLn "------------------------------------------------"
  let (cA, aA) = encodeImp (rhleProgA rhleTrip)
  let (cE, aE) = encodeImp (rhleProgE rhleTrip)
  cAStr <- printZ3 cA
  cEStr <- printZ3 cE
  putStrLn $ "A Abducibles: " ++ (show aA)
  putStrLn $ "A Encoding:\n" ++ cAStr
  putStrLn "------------------------------------------------"
  putStrLn $ "E Abducibles: " ++ (show aE)
  putStrLn $ "E Encoding:\n" ++ cEStr
  putStrLn "------------------------------------------------"
  result <- evalZ3 $ verify1 rhleTrip
  case result of
    IRSat interp -> do
      putStrLn "SUCCESS"
      putInterpMap interp
    IRUnsat ->
      putStrLn "FAILURE"
  putStrLn "------------------------------------------------"

useVerifier2 :: IO ()
useVerifier2 = do
  putStrLn "------------------------------------------------"
  putStrLn $ "Universal Program:\n" ++ (show.rhleProgA $ rhleTrip)
  putStrLn "------------------------------------------------"
  putStrLn $ "Existential Program:\n" ++ (show.rhleProgE $ rhleTrip)
  putStrLn "------------------------------------------------"
  result <- evalZ3 $ verify2 rhleTrip
  case result of
    Valid trace interp -> do
      putStrLn $ ppVTrace trace
      putStrLn "VALID iff the following executions are possible:"
      putInterpMap interp
    Invalid trace reason -> do
      putStrLn $ ppVTrace trace
      putStrLn $ "INVALID: " ++ reason
  putStrLn "------------------------------------------------"

printZ3 :: Cond -> IO String
printZ3 cond = evalZ3 $ astToString =<< condToZ3 cond

printZ3Simpl :: Cond -> IO String
printZ3Simpl cond = evalZ3 $ astToString =<<
    (simplify =<< condToZ3 (cond))


-------------------------------------
-- Useful for REPL experimentation --
-------------------------------------

progA = parseImpOrError "\
\  x1 := 3;              \
\  if x1 == 3 then       \
\    y1 := 5             \
\  else                  \
\    y1 := 500           "

progE0 = parseImpOrError "\
\  x2 := 3;              \
\  if x2 == 3 then       \
\    y2 := 5             \
\  else                  \
\    y2 := 500           "

progE = parseImpOrError "\
\  call x2 := randOddX() \
\    pre true            \
\    post x2 % 2 == 1;   \
\  if x2 == 4 then       \
\    y2 := 5             \
\  else                  \
\    y2 := 500           "

progE2 = parseImpOrError "\
\  call x2 := randOddX()  \
\    pre true             \
\    post x2 % 2 == 1;    \
\  if x2 == 3 then        \
\    call y2 := randOddY()\
\      pre true           \
\      post y2 % 2 == 1   \
\  else                   \
\    y2 := 500            "

rhleTrip = RHLETrip CTrue progA progE (CEq (V "y1") (V "y2"))
-------------------------------------
