{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.Language.FunImpTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.FunImp
import Ceili.Name
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set


x = Name "x" 0
y = Name "y" 0

add1Impl :: (FunImpl (FunImpProgram Integer))
add1Impl = FunImpl { fimpl_params = [x]
                   , fimpl_body = impAsgn y $ AAdd (AVar x) (ALit 1)
                   , fimpl_returns = [y]
                   }

add2Impl :: (FunImpl (FunImpProgram Integer))
add2Impl = FunImpl { fimpl_params = [x]
                   , fimpl_body = impSeq
                                  [ impCall "add1" [AVar x] [y]
                                  , impAsgn y $ AAdd (AVar y) (ALit 1)
                                  ]
                   , fimpl_returns = [y]
                   }

data ImplEnv = ImplEnv { ie_impls :: FunImplEnv (FunImpProgram Integer)
                       , ie_names :: Set Name
                       , ie_lits  :: Set Integer
                       }

instance FunImplLookup ImplEnv (FunImpProgram Integer) where
  lookupFunImpl (ImplEnv impls _ _) = lookupFunImpl impls

instance ImpPieContextProvider ImplEnv Integer where
  impPieCtx (ImplEnv _ names lits) = ImpPieContext Map.empty names lits

implEnv = ImplEnv { ie_impls = Map.fromList [ ("add1", add1Impl)
                                            , ("add2", add2Impl)
                                            ]
                  , ie_names = Set.empty
                  , ie_lits  = Set.empty
                  }

prog1 :: FunImpProgram Integer
prog1 = impSeq [ impCall "add1" [AVar x] [x]
               , impAsgn x $ AAdd (AVar x) (ALit 1)
               ]

prog2 :: FunImpProgram Integer
prog2 = impSeq [ impCall "add2" [AVar x] [x]
               , impAsgn x $ AAdd (AVar x) (ALit 1)
               ]


test_backwardPT = do
  result <- runCeili (envFunImp prog1) $ impBackwardPT implEnv prog1 $ Eq (Var x) (Num @Integer 2)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var x) (Num 0)

test_backwardPTNested = do
  result <- runCeili (envFunImp prog2) $ impBackwardPT implEnv prog2 $ Eq (Var x) (Num @Integer 3)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var x) (Num 0)

test_forwardPT = do
  result <- runCeili (envFunImp prog1) $ impForwardPT implEnv prog1 $ Eq (Var x) (Num @Integer 0)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var x) (Num 2)

test_forwardPTNested = do
  result <- runCeili (envFunImp prog2) $ impForwardPT implEnv prog2 $ Eq (Var x) (Num @Integer 0)
  case result of
    Left err     -> assertFailure $ show err
    Right actual -> assertImplies actual $ Eq (Var x) (Num 3)
