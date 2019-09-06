module Main where

import RHLEVerifier
import Z3.Monad

main :: IO ()
main = do
  useVerifier2

{-
useVerifier1 :: IO ()
useVerifier1 = do
  putStrLn "------------------------------------------------"
  putStrLn $ "Universal Program:\n" ++ (show.rhleProgA $ rhleTrip)
  putStrLn "------------------------------------------------"
  putStrLn $ "Existential Program:\n" ++ (show.rhleProgE $ rhleTrip)
  putStrLn "------------------------------------------------"
  (cA, aA) <- evalZ3 . encodeImp $ rhleProgA =<< rhleTrip
  (cE, aE) <- evalZ3 . encodeImp $ rhleProgE =<< rhleTrip
  putStrLn $ "A Abducibles: " ++ (show aA)
  putStrLn $ "A Encoding:\n" ++ cA
  putStrLn "------------------------------------------------"
  putStrLn $ "E Abducibles: " ++ (show aE)
  putStrLn $ "E Encoding:\n" ++ cE
  putStrLn "------------------------------------------------"
  result <- evalZ3 $ verify1 rhleTrip
  case result of
    Left err -> putStrLn $ "FAILURE: " ++ err
    Right interp -> do
      putStrLn "SUCCESS"
      putInterpMap interp
  putStrLn "------------------------------------------------"
-}

useVerifier2 :: IO ()
useVerifier2 = do
  putStrLn =<< runVerifier2 "true" progA1 progE1 "(= y1 y2)"

printZ3 :: AST -> IO String
printZ3 = evalZ3.astToString

printZ3Simpl :: AST -> IO String
printZ3Simpl ast = evalZ3 $ astToString =<< simplify ast


-------------------------------------
-- Useful for REPL experimentation --
-------------------------------------

p = printZ3
ps symbolList = mapM evalZ3 $ map getSymbolString symbolList

progA1 = parseImpOrError "\
\  x1 := 3;              \
\  if x1 == 3 then       \
\    y1 := 5             \
\  else                  \
\    y1 := 500           "

progE0 = parseImpOrError "\
\  x2 := 3;              \
\  if x2 == 4 then       \
\    y2 := 500           \
\  else                  \
\    y2 := 5             "

progE1 = parseImpOrError "     \
\  call x2 := rand()           \
\    pre {true}                \
\    post {(= (mod x2 2) 1))}; \
\  if x2 == 3 then             \
\    y2 := 5                   \
\  else                        \
\    y2 := 500                 "

progE2 = parseImpOrError "     \
\  call x2 := randOddX()       \
\    pre {true}                \
\    post {(= (mod x2 2) 1)};  \
\  if x2 == 3 then             \
\    call y2 := randOddY()     \
\      pre {(true)}            \
\      post {(= (mod y2 2) 1)} \
\  else                        \
\    y2 := 500                 "
