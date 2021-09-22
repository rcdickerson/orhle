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
import Ceili.Name
import Ceili.ProgState
import Ceili.StatePredicate
import Orhle.SpecImp
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter


------------
-- Values --
------------

data CValue = Concrete Integer
            | WithChoice { cv_choiceVars  :: Set Name
                         , cv_constraints :: Set (Assertion Integer)
                         , cv_value       :: Arith Integer
                         }
            deriving (Eq, Ord, Show)

instance Pretty CValue where
  pretty (Concrete i) = pretty i
  pretty (WithChoice cvs constraints val) = pretty val <> " | "
    <> if Set.null cvs
       then pretty $ (Set.toList constraints)
       else "E " <> pretty (Set.toList cvs) <> ". " <> pretty (Set.toList constraints)

instance AssertionParseable CValue where
  parseLiteral = integer >>= return . Concrete


-----------------------------------
-- Partial Arithmetic Evaluation --
-----------------------------------

data CValuePEval = CValuePEval { cvp_choiceVars  :: Set Name
                               , cvp_constraints :: Set (Assertion Integer)
                               , cvp_value       :: Arith Integer
                               } deriving (Eq, Show)

pevalCArith :: Arith CValue -> CValuePEval
pevalCArith carith = case carith of
  Num i     -> case i of
                 Concrete val -> CValuePEval Set.empty Set.empty $ Num val
                 WithChoice cvs constr val -> CValuePEval cvs constr val
  Var v     -> CValuePEval Set.empty Set.empty $ Var v
  Add as    -> pevalList Add as
  Sub as    -> pevalList Sub as
  Mul as    -> pevalList Mul as
  Div a1 a2 -> pevalBinop Div a1 a2
  Mod a1 a2 -> pevalBinop Mod a1 a2
  Pow a1 a2 -> pevalBinop Pow a1 a2
  where
    pevalList op as =
      let as' = map pevalCArith as
      in CValuePEval (Set.unions $ map cvp_choiceVars as')
                     (Set.unions $ map cvp_constraints as')
                     (op $ map cvp_value as')
    pevalBinop op a1 a2 = let
      CValuePEval cvs1 const1 val1 = pevalCArith a1
      CValuePEval cvs2 const2 val2 = pevalCArith a2
      in CValuePEval (Set.union cvs1 cvs2) (Set.union const1 const2) (op val1 val2)


------------------------------
-- Specification Evaluation --
------------------------------

instance Evaluable ctx
                   CValue
                   (Specification CValue, SpecCall CValue (SpecImpProgram CValue))
                   (ImpStep CValue) where
  eval _ st (spec, call) = do
    checkArglists spec call
    let (Specification params retVars choiceVars specPre specPost) = spec
    let (SpecCall _ args assignees) = call
    freshRetVars    <- envFreshen retVars
    freshChoiceVars <- envFreshen choiceVars
    let freshenVars = (substituteAll retVars freshRetVars)
                    . (substituteAll choiceVars freshChoiceVars)
    let callsitePre  = freshenVars
                     $ assertionAtState st
                     $ instantiateParams params args specPre
    let callsitePost = freshenVars
                     $ assertionAtState st
                     $ instantiateParams params args specPost
    meetsPre <- checkValidB $ if null choiceVars
                              then callsitePre
                              else Exists choiceVars $ callsitePre
    case meetsPre of
      False -> return Nothing
      True -> let
        (CAssertion callsitePreCVars callsitePreConstraints callsitePreAssertion) = toCAssertion callsitePost
        (CAssertion callsitePostCVars callsitePostConstraints callsitePostAssertion) = toCAssertion callsitePost
        choiceVars' = Set.unions [ callsitePreCVars
                                 , callsitePostCVars
                                 , Set.fromList freshChoiceVars ]
        constraints = Set.unions [ callsitePreConstraints
                                 , callsitePostConstraints
                                 , Set.fromList [callsitePreAssertion, callsitePostAssertion] ]
        stUpdater = uncurry $ updateState choiceVars' constraints
        in return . Just $ foldr stUpdater st (zip assignees freshRetVars)

updateState :: Set Name -> Set (Assertion Integer) -> Name -> Name -> ProgState CValue -> ProgState CValue
updateState choiceVars constraints assignee retVal st =
  let val = WithChoice choiceVars constraints (Var retVal)
  in Map.insert assignee val st

checkArglists :: Specification t -> (SpecCall t e) -> Ceili ()
checkArglists (Specification params retVars _ _ _) (SpecCall _ args assignees) =
  if      length args /= length params then throwError "Argument / parameter length mismatch"
  else if length assignees /= length retVars then throwError "Assignees / returns length mismatch"
  else return ()

instantiateParams :: SubstitutableArith t a => [Name] -> [AExp t] -> a -> a
instantiateParams params args a =
  let toAriths = map aexpToArith args
  in foldr (uncurry subArith) a (zip params toAriths)


----------------
-- Assertions --
----------------

data CAssertion = CAssertion { ca_choiceVars  :: Set Name
                             , ca_constraints :: Set (Assertion Integer)
                             , ca_assertion   :: Assertion Integer
                             }

toCAssertion :: Assertion CValue -> CAssertion
toCAssertion cvAssertion = case cvAssertion of
  ATrue     -> CAssertion Set.empty Set.empty ATrue
  AFalse    -> CAssertion Set.empty Set.empty AFalse
  Atom v    -> CAssertion Set.empty Set.empty (Atom v)
  Not a     -> let (CAssertion cv constr a') = toCAssertion a
               in CAssertion cv constr $ Not a'
  And as    -> let as' = map toCAssertion as
               in CAssertion (Set.unions $ map ca_choiceVars as')
                             (Set.unions $ map ca_constraints as')
                             (And $ map ca_assertion as')
  Or  as    -> let as' = map toCAssertion as
               in CAssertion (Set.unions $ map ca_choiceVars as')
                             (Set.unions $ map ca_constraints as')
                             (Or $ map ca_assertion as')
  Imp a1 a2 -> let
                 CAssertion cv1 constr1 a1' = toCAssertion a1
                 CAssertion cv2 constr2 a2' = toCAssertion a2
               in CAssertion (Set.union cv1 cv2) (Set.union constr1 constr2) (Imp a1' a2')
  Eq  a1 a2 -> cmpCAssertion Eq  a1 a2
  Lt  a1 a2 -> cmpCAssertion Lt  a1 a2
  Gt  a1 a2 -> cmpCAssertion Gt  a1 a2
  Lte a1 a2 -> cmpCAssertion Lte a1 a2
  Gte a1 a2 -> cmpCAssertion Gte a1 a2
  Forall vars a -> let CAssertion cv constr a' = toCAssertion a
                   in CAssertion cv constr $ Forall vars a'
  Exists vars a -> let CAssertion cv constr a' = toCAssertion a
                   in CAssertion cv constr $ Exists vars a'
  where
    cmpCAssertion op a1 a2 =
      let
        CValuePEval cvs1 constr1 val1 = pevalCArith a1
        CValuePEval cvs2 constr2 val2 = pevalCArith a2
      in CAssertion (Set.union cvs1 cvs2) (Set.union constr1 constr2) (op val1 val2)

instance SMTQueryable CValue where
  buildSMTQuery assertion =
    let
      CAssertion choiceVars constraints iassertion = toCAssertion assertion
      allAssertions = And (iassertion:(Set.toList constraints))
      query = if Set.null choiceVars
              then allAssertions
              else Exists (Set.toList choiceVars) $ allAssertions
    in buildSMTQuery query

verifyCAssertion :: Assertion CValue -> Ceili Bool
verifyCAssertion assertion = do
  let (CAssertion choiceVars constraints cassertion) = toCAssertion assertion
  let check = And $ cassertion:(Set.toList constraints)
  if Set.null choiceVars
    then return $ eval @() @Integer () Map.empty check
    else checkValidB $ Exists (Set.toList choiceVars) check

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
  (Concrete i, WithChoice cvars constraints val) ->
    WithChoice cvars constraints $ fabs (Num i) val
  (WithChoice cvars constraints val, Concrete j) ->
    WithChoice cvars constraints $ fabs val (Num j)
  (WithChoice lcvars lconstraints lval, WithChoice rcvars rconstraints rval) ->
    WithChoice (Set.union lcvars rcvars)
               (Set.union lconstraints rconstraints)
               (fabs lval rval)

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
  testState = flip $ evalCAssertion
