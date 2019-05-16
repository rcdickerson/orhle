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
func1 = UFunc "f1" ["z"] ((V "x") :=: (I 0)) ((V "z") :=: (I 3))
func2 = UFunc "f2" ["z"] BTrue ((V "z") :=: ((V "x") :+: (I 3)))
funcRand = UFunc "rand" [] BTrue BTrue
prog1 = Seq ["x" := (I 0), "y" := (I 0), Call func2]
prog2 = Seq ["x" := (I 0), "y" := (I 0), Call funcRand]
cond1 = CEq (V "z") (I 3)
htrip1 = HLTrip CTrue prog1 cond1
htrip2 = HLTrip CTrue prog2 cond1
hetrip1 = HLETrip CTrue prog1 cond1
hetrip2 = HLETrip CTrue prog2 cond1

-------
randOdd x = UFunc "randOdd" [] BTrue (AMod x (I 2) :=: (I 1))

progA = Seq [ "x1" := (I 5)
            , If ((V "x1") :=: (I 5))
                   ("y1" := (I 3))
                   ("y1" := (I 300))
            ]
progE = Seq [ Call (randOdd (V "x2"))
            , If ((V "x2") :=: (I 5))
                   ("y2" := (I 3))
                   ("y2" := (I 300))
            ]
rhleTrip = RHLETrip CTrue progA progE (CEq (V "y1") (V "y2"))
-------

printZ3 :: [Cond] -> IO String
printZ3 conds = evalZ3 $ astToString =<< (simplify =<< condToZ3 (foldl CAnd CTrue (conds)))
