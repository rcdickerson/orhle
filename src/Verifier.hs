module Verifier where

import Conditions
import Hoare
import HoareE
import Imp
import RHLE
import Z3.Monad

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

printZ3 :: [Cond] -> IO String
printZ3 conds = evalZ3 $ astToString =<< condToZ3 (foldl CAnd CTrue (conds))

printZ3Simp :: [Cond] -> IO String
printZ3Simp conds = evalZ3 $ astToString =<< (simplify =<< condToZ3 (foldl CAnd CTrue (conds)))
