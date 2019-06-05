module Main where

import Lib
import qualified Data.Map as Map
import Z3.Monad

main :: IO ()
main = useVerifier1

useVerifier1 :: IO ()
useVerifier1 = do
  putStrLn "------------------------------------------------"
  putStrLn $ "Universal Program:\n" ++ (show progA)
  putStrLn "------------------------------------------------"
  putStrLn $ "Existential Program:\n" ++ (show progE)
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
{-
  let (cA, aA) = encodeImp (rhleProgA rhleTrip)
  let (cE, aE) = encodeImp (rhleProgE rhleTrip)
  let fPosts = conjoin $ map (fPostCond.func) (aA ++ aE)
  preConds  <- evalZ3 $ mapM condToZ3 [rhlePre rhleTrip, cA, cE]
  postConds <- evalZ3 $ mapM condToZ3 [rhlePost rhleTrip, fPosts]
  result <- evalZ3 $ abduce (aA ++ aE, preConds, postConds)
  putStrLn $ "Abduction result: " ++ (show result)
  putStrLn "------------------------------------------------"
-}
  result <- evalZ3 $ verify1 rhleTrip
  case result of
    IRSat interp -> do
      putStrLn "SUCCESS"
      let putInterpLine = \(duc, ast) -> do
            let ducName = fName.func $ duc
            interp <- evalZ3 $ astToString ast
            putStrLn $ "  " ++ ducName ++ ": " ++ interp
      mapM_ putInterpLine (Map.toList interp)
    IRUnsat ->
      putStrLn "FAILURE"
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

progE = parseImpOrError "\
\  call x2 := randOddX() \
\    pre true            \
\    post x2 % 2 == 1;   \
\  if x2 == 3 then       \
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
