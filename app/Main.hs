module Main where

import Lib
import Z3.Monad

main :: IO ()
main = do
  putStrLn "------------------------------------------------"
  putStrLn $ "Universal Program:\n" ++ (show progA)
  putStrLn "------------------------------------------------"
  putStrLn $ "Existential Program:\n" ++ (show progE)
  putStrLn "------------------------------------------------"
  let (cA, aA) = encodeImp progA
  let (cE, aE) = encodeImp progE
  cAStr <- printZ3 cA
  cEStr <- printZ3 cE
  putStrLn $ "A Abducibles: " ++ (show aA)
  putStrLn $ "A Encoding:\n" ++ cAStr
  putStrLn "------------------------------------------------"
  putStrLn $ "E Abducibles: " ++ (show aE)
  putStrLn $ "E Encoding:\n" ++ cEStr
  putStrLn "------------------------------------------------"
  result <- evalZ3 $ verify1 rhleTrip
  putStrLn $ "Verifies: " ++ (show result)
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
\    y1 := 3             \
\  else                  \
\    y1 := 300           "

progE = parseImpOrError "\
\  call randOdd(x2)      \
\    pre true            \
\    post x2 % 2 == 1;   \
\  if x2 == 5 then       \
\    y2 := 3             \
\  else                  \
\    y2 := 300           "

rhleTrip = RHLETrip CTrue progA progE (CEq (V "y1") (V "y2"))
-------------------------------------
