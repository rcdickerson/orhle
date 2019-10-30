module Main where

import Orhle
import Z3.Monad

main :: IO ()
main = do runSimpleExample

runSimpleExample :: IO ()
runSimpleExample = do
  let (progA, specA) = exampleA1
  let (progE, specE) = exampleE1
  putStrLn =<< runVerifier singleAbdVerifier "true" [progA] [progE] "(= y1 y2)"

-------------------------------------
-- Useful for REPL experimentation --
-------------------------------------

printZ3 :: AST -> IO String
printZ3 = evalZ3.astToString

printZ3Simpl :: AST -> IO String
printZ3Simpl ast = evalZ3 $ astToString =<< simplify ast

p = printZ3
ps symbolList = mapM evalZ3 $ map getSymbolString symbolList

exampleA1 = parseImpOrError "\
\  x1 := 3;              \
\  if x1 == 3 then       \
\    y1 := 5             \
\  else                  \
\    y1 := 500           "

exampleE0 = parseImpOrError "\
\  x2 := 3;              \
\  if x2 == 3 then       \
\    y2 := 500           \
\  else                  \
\    y2 := 5             "

exampleE1 = parseImpOrError "     \
\  call x2 := rand()           \
\    pre {true}                \
\    post {(= (mod x2 2) 1))}; \
\  if x2 == 3 then             \
\    y2 := 5                   \
\  else                        \
\    y2 := 500                 "

exampleE2 = parseImpOrError "     \
\  call x2 := randOddX()       \
\    pre {true}                \
\    post {(= (mod x2 2) 1)};  \
\  if x2 == 3 then             \
\    call y2 := randOddY()     \
\      pre {true}              \
\      post {(= (mod y2 2) 1)} \
\  else                        \
\    y2 := 500                 "


------------------------------------
-- Some hard-coded klive examples --
------------------------------------

runSimpleNonRefinement :: IO ()
runSimpleNonRefinement = do
--  fails: forall t1. exists t2.
--    t1|refinement == t2|original;
  let (progOriginal, specOriginal) = parseImpOrError "  \
  \  call t1_x := t1_randInt()          \
  \     pre {true}                      \
  \     post {(= t1_x 20)}"
  let (progRefinement, specRefinement) = parseImpOrError " \
  \  call t2_x := t2_randInt()           \
  \     pre {true}                       \
  \     post {(and (>= t2_x 0) (< t2_x 10))}"
  putStrLn =<< runVerifier singleAbdVerifier "true" [progRefinement] [progOriginal] "(= t1_x t2_x)"

runSimpleRefinement :: IO ()
runSimpleRefinement = do
--  satisfies: forall t1. exists t2.
--    t1|refinement == t2|original;
  let (progOriginal, specOriginal) = parseImpOrError "  \
  \  call t1_x := t1_randInt()    \
  \     pre {true}                      \
  \     post {(and (>= t1_x 0) (< t1_x 20))}"
  let (progRefinement, specRefinement) = parseImpOrError " \
  \  call t2_x := t2_randInt()    \
  \     pre {true}                       \
  \     post {(and (>= t2_x 0) (< t2_x 10))}"
  putStrLn =<< runVerifier singleAbdVerifier "true" [progRefinement] [progOriginal] "(= t1_x t2_x)"
