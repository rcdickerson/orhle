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
  let setup@(ducs, lhs, post) = setupAbduction rhleTrip
  lhsStr <- printZ3 (conjoin lhs)
  postStr <- printZ3 post
  putStrLn $ "Abducibles:" ++ (show ducs)
  putStrLn $ "Abduction LHS:\n" ++ lhsStr
  putStrLn $ "Abduction Post: " ++ postStr
  putStrLn "------------------------------------------------"
  abdResult <- evalZ3 $ astToString =<< (abduce setup)
  putStrLn $ "Abduction Result:\n" ++ abdResult
  putStrLn "------------------------------------------------"
  result <- evalZ3 $ verify rhleTrip
  putStrLn $ "Verifies: " ++ (show result)
  putStrLn "------------------------------------------------"

printZ3 :: Cond -> IO String
printZ3 cond = evalZ3 $ astToString =<< condToZ3 cond

printZ3Simpl :: Cond -> IO String
printZ3Simpl cond = evalZ3 $ astToString =<<
    (simplify =<< condToZ3 (cond))

parseImpOrError :: String -> Stmt
parseImpOrError str = case (parseImp str) of
  Left e -> error e
  Right stmt -> stmt


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
