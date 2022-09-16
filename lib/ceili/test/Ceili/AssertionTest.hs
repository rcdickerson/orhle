{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.AssertionTest(htf_thisModulesTests) where
import Test.Framework

import qualified Data.Set as Set
import Ceili.Assertion
import Ceili.Name
import Ceili.SMTString

-- Some dummy names and assertions for convenience.
x0 = Name "x" 0
x1 = Name "x" 1
x2 = Name "x" 2
y0 = Name "y" 0
sc8875 = Name "SC" 8875


assertion1 :: Assertion Integer
assertion1 = Not $ And [ Eq (Var x0) (Add [Num 5, Var y0])
                       , Lt (Var x1) (Var x2)
                       ]
assertion1SMT = "(not (and (= x (+ 5 y)) (< x!1 x!2)))"

assertion2 :: Assertion Integer
assertion2 = Forall [x0, y0] $ Exists [x1] $ Lt (Var x1) (Var x2)
assertion2SMT = "(forall ((x Int) (y Int)) (exists ((x!1 Int)) (< x!1 x!2)))"

assertion3 :: Assertion Integer
assertion3 = And [And [Exists [Name "z" 5990]
                       (Imp (Atom sc8875) AFalse)]]
assertion3SMT = "(and (and (exists ((z!5990 Int)) (=> SC!8875 false))))"

test_freeVars = do
  assertEqual (Set.fromList [x0, x1, x2, y0]) (freeVars assertion1)
  assertEqual (Set.fromList [x2]) (freeVars assertion2)

test_showSMT = do
  assertEqual assertion1SMT $ showSMT assertion1
  assertEqual assertion2SMT $ showSMT assertion2
  assertEqual assertion3SMT $ showSMT assertion3
  assertEqual "(< -1 1)" $ showSMT (Lt @Integer (Num (-1)) (Num 1))

test_parseAssertion = do
  assertEqual (Right assertion1) $ parseAssertion assertion1SMT
  assertEqual (Right assertion2) $ parseAssertion assertion2SMT
  assertEqual (Right assertion3) $ parseAssertion assertion3SMT
  assertEqual (Right $ Lt (Num (-1)) (Num 1)) $ parseAssertion @Integer "(< -1 1)"

test_parseModel = do
  assertEqual (Right $ And @Integer [Eq (Var y0) (Num 1), Eq (Var x0) (Num 0)])
              (parseAssertion "(model (define-fun y () Int 1) (define-fun x () Int 0) )")

test_subArith = do
  assertEqual ( Not $ And [ Eq (Add [Var x0, Num 1]) (Add [Num 5, Var y0])
                       , Lt (Var x1) (Var x2)] )
              ( subArith @Integer x0 (Add [ Var x0, Num 1 ]) assertion1 )
  assertEqual ( Forall [x0, y0] $ Exists [x1] $ Lt (Var x1) (Var x2) )
              ( subArith @Integer x0 (Add [ Var x0, Num 1 ]) assertion2 )
  assertEqual ( And [And [Exists [Name "z" 5990]
                       (Imp (Atom sc8875) AFalse)]])
              ( subArith @Integer sc8875 (Add [ Var x0, Num 1 ]) assertion3 )
  let assertion3' = And [And [Exists [Name "z" 5990]
                       (Imp (Eq (Var x0) (Var x1)) AFalse)]]
  assertEqual ( And @Integer [And [Exists [Name "z" 5990]
                       (Imp (Eq (Add [Var x0, Num 1]) (Var x1)) AFalse)]])
              ( subArith @Integer x0 (Add [ Var x0, Num 1 ]) assertion3' )

test_negativeNumber = do
  assertEqual (Right $ Eq @Integer (Num $ -5) (Var x0))
              (parseAssertion "(= -5 x)")

test_negativeNumberInParens = do
  assertEqual (Right $ Eq @Integer (Num $ -5) (Var x0))
              (parseAssertion "(= (-5) x)")

test_negativeNumberInModel = do
  assertEqual (Right $ Eq @Integer (Var x0) (Num $ -1))
              (parseAssertion "(model (define-fun x () Int (- 1 ) ))")
