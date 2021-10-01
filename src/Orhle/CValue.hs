{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CValue
  ( CValue(..)
  , CValuePEval(..)
  , pevalCArith
  ) where

import Ceili.Assertion
import Ceili.Assertion.AssertionParser ( integer )
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Evaluation
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Name
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Orhle.SpecImp
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map
import Prettyprinter

import Debug.Trace

------------
-- Values --
------------

data CValue = Concrete Integer
            | Constrained { cv_value        :: Arith Integer
                          , cv_choiceVars   :: Set Name
                          , cv_aConstraints :: Set (Assertion Integer)
                          , cv_eConstraints :: Set (Assertion Integer)
                          }
            deriving (Eq, Ord, Show)

instance Pretty CValue where
  pretty (Concrete i) = pretty i
  pretty (Constrained val cvs aconstrs econstrs) =
    let
      prettyCvs = case Set.null cvs of
                    True  -> emptyDoc
                    False -> pretty @String "∃" <+> (list . (map pretty) . Set.toList $ cvs) <> "."
      prettyAConstrs = list (map pretty $ Set.toList aconstrs)
      prettyEConstrs = prettyCvs <+> list (map pretty $ Set.toList econstrs)
    in case (Set.null aconstrs, Set.null econstrs) of
      (True, True)   -> pretty val
      (False, True)  -> pretty val <+> "a|" <+> prettyAConstrs
      (True, False)  -> pretty val <+> "e|" <+> prettyEConstrs
      (False, False) -> pretty val <+> "(a,e)|" <+> prettyAConstrs <+> "==>" <+> prettyEConstrs

instance AssertionParseable CValue where
  parseLiteral = integer >>= return . Concrete


-----------------------------------
-- Partial Arithmetic Evaluation --
-----------------------------------

data CValuePEval = CValuePEval { cvp_value        :: Arith Integer
                               , cvp_choiceVars   :: Set Name
                               , cvp_aConstraints :: Set (Assertion Integer)
                               , cvp_eConstraints :: Set (Assertion Integer)
                               } deriving (Eq, Show)

pevalCArith :: Arith CValue -> CValuePEval
pevalCArith carith = case carith of
  Num i     -> case i of
                 Concrete val -> CValuePEval (Num val) Set.empty Set.empty Set.empty
                 Constrained val cvs aconstrs econstrs -> CValuePEval val cvs aconstrs econstrs
  Var v     -> CValuePEval (Var v) Set.empty Set.empty Set.empty
  Add as    -> pevalList Add as
  Sub as    -> pevalList Sub as
  Mul as    -> pevalList Mul as
  Div a1 a2 -> pevalBinop Div a1 a2
  Mod a1 a2 -> pevalBinop Mod a1 a2
  Pow a1 a2 -> pevalBinop Pow a1 a2
  where
    pevalList op as =
      let as' = map pevalCArith as
      in CValuePEval (op $ map cvp_value as')
                     (Set.unions $ map cvp_choiceVars as')
                     (Set.unions $ map cvp_aConstraints as')
                     (Set.unions $ map cvp_eConstraints as')
    pevalBinop op a1 a2 = let
      CValuePEval val1 cvs1 aconstrs1 econstrs1 = pevalCArith a1
      CValuePEval val2 cvs2 aconstrs2 econstrs2 = pevalCArith a2
      in CValuePEval (op val1 val2)
                     (Set.union cvs1 cvs2)
                     (Set.union aconstrs1 aconstrs2)
                     (Set.union econstrs1 econstrs2)


------------------------------
-- Specification Evaluation --
------------------------------

instance Evaluable ctx
                   CValue
                   (SpecImpQuant, Specification CValue, SpecCall CValue (SpecImpProgram CValue))
                   (ImpStep CValue) where
  eval _ st (quant, spec, call) = do
    checkArglists spec call
    let (Specification params retVars choiceVars specPre specPost) = spec
    let (SpecCall _ args assignees) = call
    freshRetVars      <- envFreshen retVars
    freshChoiceVars   <- envFreshen choiceVars
    let freshenVars   = (substituteAll retVars freshRetVars)
                      . (substituteAll choiceVars freshChoiceVars)
    let vCallsitePre  = freshenVars
                      $ assertionAtState st
                      $ instantiateParams params args specPre
    let vCallsitePost = freshenVars
                      $ assertionAtState st
                      $ instantiateParams params args specPost
    meetsPre <- verifyCAssertion $ case null freshChoiceVars of
                                     True  -> vCallsitePre
                                     False -> Exists freshChoiceVars vCallsitePre
    case meetsPre of
      False -> return []
      True -> let
        cvs = Set.fromList freshChoiceVars
        (CAssertion callsiteAssertion callsiteCvs callsiteAConstrs callsiteEConstrs)
          = toCAssertion $ aAnd [vCallsitePre, vCallsitePost]
        constrValue retVar = case quant of
            SIQ_Universal   -> Constrained (Var retVar)
                                           (Set.union cvs callsiteCvs)
                                           (Set.insert callsiteAssertion callsiteAConstrs)
                                           callsiteEConstrs
            SIQ_Existential -> Constrained (Var retVar)
                                           (Set.unions [cvs, callsiteCvs, Set.fromList freshRetVars])
                                           callsiteAConstrs
                                           (Set.insert callsiteAssertion callsiteEConstrs)
        stUpdater (assignee, retVar) = Map.insert assignee (constrValue retVar)
        in return [foldr stUpdater st (zip assignees freshRetVars)]

checkArglists :: Specification t -> (SpecCall t e) -> Ceili ()
checkArglists (Specification params retVars _ _ _) (SpecCall _ args assignees) =
  if      length args /= length params then throwError "Argument / parameter length mismatch"
  else if length assignees /= length retVars then throwError "Assignees / returns length mismatch"
  else return ()

instantiateParams :: SubstitutableArith t a => [Name] -> [AExp t] -> a -> a
instantiateParams params args a =
  let toAriths = map aexpToArith args
  in foldr (uncurry subArith) a (zip params toAriths)


-----------
-- BExps --
-----------

instance SplitOnBExp CValue where
  splitOnBExp bexp st = do
    let assertion = assertionAtState st $ bexpToAssertion bexp
    canBeTrue  <- checkValidB assertion
    canBeFalse <- checkValidB $ Not assertion
    return $ ( if canBeFalse then Just st else Nothing
             , if canBeTrue  then Just st else Nothing )


----------------
-- Assertions --
----------------

data CAssertion = CAssertion { ca_assertion    :: Assertion Integer
                             , ca_choiceVars   :: Set Name
                             , ca_aConstraints :: Set (Assertion Integer)
                             , ca_eConstraints :: Set (Assertion Integer)
                             }

unconstrainedCAssertion :: Assertion Integer -> CAssertion
unconstrainedCAssertion a = CAssertion a Set.empty Set.empty Set.empty

toCAssertion :: Assertion CValue -> CAssertion
toCAssertion cvAssertion = case cvAssertion of
  ATrue     -> unconstrainedCAssertion ATrue
  AFalse    -> unconstrainedCAssertion AFalse
  Atom v    -> unconstrainedCAssertion (Atom v)
  Not a     -> let (CAssertion assertion cvs aconstrs econstrs) = toCAssertion a
               in CAssertion (Not assertion) cvs aconstrs econstrs
  And as    -> let cas = map toCAssertion as
               in CAssertion (And $ map ca_assertion cas)
                             (Set.unions $ map ca_choiceVars cas)
                             (Set.unions $ map ca_aConstraints cas)
                             (Set.unions $ map ca_eConstraints cas)
  Or  as    -> let cas = map toCAssertion as
               in CAssertion (Or $ map ca_assertion cas)
                             (Set.unions $ map ca_choiceVars cas)
                             (Set.unions $ map ca_aConstraints cas)
                             (Set.unions $ map ca_eConstraints cas)
  Imp a1 a2 -> let
                 (CAssertion ca1 cvs1 aconstrs1 econstrs1) = toCAssertion a1
                 (CAssertion ca2 cvs2 aconstrs2 econstrs2) = toCAssertion a2
               in CAssertion (Imp ca1 ca2)
                             (Set.union cvs1 cvs2)
                             (Set.union aconstrs1 aconstrs2)
                             (Set.union econstrs1 econstrs2)
  Eq  a1 a2 -> convertArith Eq  a1 a2
  Lt  a1 a2 -> convertArith Lt  a1 a2
  Gt  a1 a2 -> convertArith Gt  a1 a2
  Lte a1 a2 -> convertArith Lte a1 a2
  Gte a1 a2 -> convertArith Gte a1 a2
  Forall vars a -> let (CAssertion ca cvs aconstrs econstrs) = toCAssertion a
                   in CAssertion (Forall vars $ ca) cvs aconstrs econstrs
  Exists vars a -> let (CAssertion ca cvs aconstrs econstrs) = toCAssertion a
                   in CAssertion (Exists vars $ ca) cvs aconstrs econstrs
  where
    convertArith op arith1 arith2 =
      let
        (CValuePEval val1 cvs1 aconstrs1 econstrs1) = pevalCArith arith1
        (CValuePEval val2 cvs2 aconstrs2 econstrs2) = pevalCArith arith2
        in CAssertion (op val1 val2)
                      (Set.union cvs1 cvs2)
                      (Set.union aconstrs1 aconstrs2)
                      (Set.union econstrs1 econstrs2)

verifyCAssertion :: Assertion CValue -> Ceili Bool
verifyCAssertion assertion = checkValidB assertion

instance ValidCheckable CValue where
  checkValid logger cvAssertion = let
    (CAssertion assertion cvs aconstrsSet econstrsSet) = toCAssertion cvAssertion
    aconstrs = aAnd $ Set.toList aconstrsSet
    econstrs = aAnd $ Set.toList econstrsSet
    quantEConstrs = case Set.null cvs of
                      True -> aAnd [econstrs, assertion]
                      False -> Exists (Set.toList cvs) $ aAnd [econstrs, assertion]
    in SMT.checkValid logger $ aImp aconstrs quantEConstrs


---------------------------
-- Arithmetic Operations --
---------------------------

instance Embeddable Integer CValue where embed = Concrete

cvalAdd :: CValue -> CValue -> CValue
cvalAdd = cvalBinop (+) (\l r -> Add [l, r])

cvalSub :: CValue -> CValue -> CValue
cvalSub = cvalBinop (-) (\l r -> Sub [l, r])

cvalMul :: CValue -> CValue -> CValue
cvalMul = cvalBinop (*) (\l r -> Mul [l, r])

cvalDiv :: CValue -> CValue -> CValue
cvalDiv = cvalBinop quot Div

cvalExp :: CValue -> CValue -> CValue
cvalExp = cvalBinop (^) Pow

cvalMod :: CValue -> CValue -> CValue
cvalMod = cvalBinop mod Mod

cvalBinop :: (Integer -> Integer -> Integer)
          -> (Arith Integer -> Arith Integer -> Arith Integer)
          -> CValue -> CValue -> CValue
cvalBinop fconc fabs lhs rhs = case (lhs, rhs) of
  (Concrete i, Concrete j) ->
    Concrete $ fconc i j
  (Concrete i, Constrained val cvars aconstrs econstrs) ->
    Constrained (fabs (Num i) val) cvars aconstrs econstrs
  (Constrained val cvars aconstrs econstrs, Concrete j) ->
    Constrained (fabs val (Num j)) cvars aconstrs econstrs
  (Constrained lval lcvars laconstrs leconstrs, Constrained rval rcvars raconstrs reconstrs) ->
    Constrained (fabs lval rval)
                (Set.union lcvars rcvars)
                (Set.union laconstrs raconstrs)
                (Set.union leconstrs reconstrs)

instance AExpAlgebra CValue where
  aeZero = Concrete 0
  aeAdd  = cvalAdd
  aeSub  = cvalSub
  aeMul  = cvalMul
  aeDiv  = cvalDiv
  aeExp  = cvalExp
  aeMod  = cvalMod

instance ArithAlgebra CValue where
  arZero = Concrete 0
  arOne  = Concrete 1
  arAdd  = cvalAdd
  arSub  = cvalSub
  arMul  = cvalMul
  arDiv  = cvalDiv
  arExp  = cvalExp
  arMod  = cvalMod


---------------------
-- State Predicate --
---------------------

evalCAssertion :: ProgState CValue -> Assertion CValue -> Ceili Bool
evalCAssertion state assertion = verifyCAssertion $ assertionAtState state assertion

instance Evaluable c CValue (Assertion CValue) (Ceili Bool) where
  eval _ = evalCAssertion

instance StatePredicate (Assertion CValue) CValue where
  testState = flip evalCAssertion
