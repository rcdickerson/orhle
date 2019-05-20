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

-------------------------------------
-- Useful for REPL experimentation --
-------------------------------------
randOdd x = UFunc "randOdd" [x] BTrue (AMod (V x) (I 2) :=: (I 1))

progA = Seq [ "x1" := (I 5)
            , If ((V "x1") :=: (I 5))
                   ("y1" := (I 3))
                   ("y1" := (I 300))
            ]
progE = Seq [ Call (randOdd "x2")
            , If ((V "x2") :=: (I 5))
                   ("y2" := (I 3))
                   ("y2" := (I 300))
            ]
rhleTrip = RHLETrip CTrue progA progE (CEq (V "y1") (V "y2"))
-------------------------------------
