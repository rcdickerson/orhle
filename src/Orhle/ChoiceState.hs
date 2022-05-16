{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.ChoiceState
  (
  ) where

import Ceili.Assertion
import Ceili.Assertion.AssertionParser ( integer )
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Evaluation
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import Orhle.SpecImp


-------------------
-- Choice Values --
-------------------

data ChoiceValue t = Concrete t
                   | Choice { choiceValue    :: Arith t
                            , choiceVars     :: [Name]
                            , choiceAConstrs :: [Assertion t]
                            , choiceEConstrs :: [Assertion t]
                            }


--------------------------------------------------------
-- Instances Needed for Evaluation on Integer Choices --
--------------------------------------------------------

instance Embeddable Integer (ChoiceValue Integer) where
  embed = Concrete

instance AssertionParseable (ChoiceValue Integer) where
  parseLiteral = pure . Concrete =<< integer

instance AExpAlgebra (ChoiceValue Integer) where
  aeZero = Concrete 0
  aeAdd  = intChoiceOp (+)  $ \v1 v2 -> Add [v1, v2]
  aeSub  = intChoiceOp (-)  $ \v1 v2 -> Sub [v1, v2]
  aeMul  = intChoiceOp (*)  $ \v1 v2 -> Mul [v1, v2]
  aeDiv  = intChoiceOp quot Div
  aeExp  = intChoiceOp (^)  Pow
  aeMod  = intChoiceOp mod  Mod

intChoiceOp :: (Integer -> Integer -> Integer)
            -> (Arith Integer -> Arith Integer -> Arith Integer)
            -> ChoiceValue Integer
            -> ChoiceValue Integer
            -> ChoiceValue Integer
intChoiceOp intF arithF choice1 choice2 =
  case (choice1, choice2) of
    (Concrete i1, Concrete i2) ->
      Concrete $ intF i1 i2
    (Concrete i1, Choice val cvars aconstrs econstrs) ->
      Choice (arithF (Num i1) val) cvars aconstrs econstrs
    (Choice val cvars aconstrs econstrs, Concrete i2) ->
      Choice (arithF val (Num i2)) cvars aconstrs econstrs
    (Choice val1 cvars1 aconstrs1 econstrs1, Choice val2 cvars2 aconstrs2 econstrs2) ->
      Choice (arithF val1 val2) (cvars1 ++ cvars2) (aconstrs1 ++ aconstrs2) (econstrs1 ++ econstrs2)

instance ValidCheckable (ChoiceValue Integer) where
  checkValid logger assertion =
    let (aconstrs, econstrs) = toSMTQuery assertion
        query = Imp aconstrs econstrs
    in error ""

toSMTQuery :: Assertion (ChoiceValue Integer) -> (Assertion Integer, Assertion Integer)
toSMTQuery cvAssertion = let
  (CAssertion assertion cvs aconstrsSet econstrsSet) = toCAssertion cvAssertion
  aconstrs = aAnd $ Set.toList aconstrsSet
  econstrs = aAnd $ Set.toList econstrsSet
  quantEConstrs = case Set.null cvs of
                    True -> aAnd [econstrs, assertion]
                    False -> Exists (Set.toList cvs) $ aAnd [econstrs, assertion]
  in (aconstrs, quantEConstrs)

instance SplitOnBExp (ChoiceValue Integer) where
  splitOnBExp bexp st = do
    let assertion = assertionAtState st $ bexpToAssertion bexp
    canBeTrue  <- checkValidB assertion
    canBeFalse <- checkValidB $ Not assertion
    return $ ( if canBeFalse then Just st else Nothing
             , if canBeTrue  then Just st else Nothing )
    error "unimplemented"


-----------------
-- Reification --
-----------------

type ChoiceStrategy t = Map String (Arith t)

data ReifiedChoice t = Impossible
                     | ReifiedChoice { reifiedValue :: t }

reifyChoice :: ChoiceStrategy t -> ChoiceValue t -> ReifiedChoice t
reifyChoice strategy value =
  case value of
    Concrete t -> ReifiedChoice t
    Choice value cvars aconstrs econstrs ->
      let
        choose cvar = case Map.lookup (nHandle cvar) strategy of
                        Nothing  -> Nothing
                        Just val -> Just (cvar, val)
        choices = catMaybes $ map choose cvars
        reifiedVal = foldr (uncurry subArith) value choices
        reifyConstraint constr = foldr (uncurry subArith) constr choices
        reifiedAConstrs = map reifyConstraint aconstrs
        reifiedEConstrs = map reifyConstraint econstrs
      in error "unimplemented"

reifyState :: ChoiceStrategy t -> ProgState (ChoiceValue t) -> Maybe (ProgState t)
reifyState strategy choiceState = error "unimplemented"
