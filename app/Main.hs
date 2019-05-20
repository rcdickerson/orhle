module Main where

import Lib
import Z3.Monad

main :: IO ()
main = do
  putStrLn $ "Universal Program:\n" ++ (show progA)
  putStrLn $ "Existential Program:\n" ++ (show progE)
  vcs <- printZ3 $ rhleVCs rhleTrip
  putStrLn $ "Verification Conditions:\n" ++ vcs

printZ3 :: [Cond] -> IO String
printZ3 conds = evalZ3 $ astToString =<< condToZ3 (foldl CAnd CTrue (conds))

printZ3Simp :: [Cond] -> IO String
printZ3Simp conds = evalZ3 $ astToString =<< (simplify =<< condToZ3 (foldl CAnd CTrue (conds)))

parseImpOrError :: String -> Stmt
parseImpOrError str = case (parseImp str) of
  Left e -> error e
  Right stmt -> stmt


-------------------------------------
-- Useful for REPL experimentation --
-------------------------------------
randOdd x = UFunc "randOdd" [x] BTrue (AMod (V x) (I 2) :=: (I 1))

progA = parseImpOrError "\
\  x1 := 5;              \
\  if x1 == 5 then       \
\    y1 := 3             \
\  else                  \
\    y1 := 300"

progE = parseImpOrError "\
\  func randOdd(x2)      \
\    pre true            \
\    post x2 % 2 == 1;   \
\  if x2 == 5 then       \
\    y2 := 3             \
\  else                  \
\    y2 := 300           "

rhleTrip = RHLETrip CTrue progA progE (CEq (V "y1") (V "y2"))
-------------------------------------
