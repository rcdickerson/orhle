{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.Language.AExpParserTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Language.AExp
import Ceili.Language.AExpParser
import Ceili.Name
import Text.Parsec

runParse :: AExpParseable t => String -> IO (AExp t)
runParse str = case runParser parseAExp () "" str of
                 Left err -> assertFailure $ show err
                 Right aexp -> return aexp

x = Name "x" 0
y = Name "y" 0
z = Name "z" 0

test_parseName = do
  let expected = AVar $ Name "x" 0
  actual <- runParse @Integer "x"
  assertEqual expected actual

test_parseNameWithIndex = do
  let expected = AVar $ Name "x" 12
  actual <- runParse @Integer "x!12"
  assertEqual expected actual

test_parseInt = do
  let expected = ALit 42
  actual <- runParse @Integer "42"
  assertEqual expected actual

test_parseAdd = do
  let expected = AAdd (AVar x) (ALit 42)
  actual <- runParse @Integer "x + 42"
  assertEqual expected actual

test_parseAdd2 = do
  let expected = AAdd (ALit 42) (AVar x)
  actual <- runParse @Integer "42 + x"
  assertEqual expected actual

test_parseSub = do
  let expected = ASub (AVar x) (ALit 42)
  actual <- runParse @Integer "x - 42"
  assertEqual expected actual

test_parsePow = do
  let expected = APow (AVar x) (ALit 42)
  actual <- runParse @Integer "x ^ 42"
  assertEqual expected actual

test_parseMul = do
  let expected = AMul (AVar x) (ALit 42)
  actual <- runParse @Integer "x * 42"
  assertEqual expected actual

test_parseDiv = do
  let expected = ADiv (AVar x) (ALit 42)
  actual <- runParse @Integer "x / 42"
  assertEqual expected actual

test_parseMod = do
  let expected = AMod (AVar x) (ALit 42)
  actual <- runParse @Integer "x % 42"
  assertEqual expected actual

test_parseNested = do
  let expected = AMul (AAdd (AVar x) (AVar y)) (AVar z)
  actual <- runParse @Integer "(x + y) * z"
  assertEqual expected actual
