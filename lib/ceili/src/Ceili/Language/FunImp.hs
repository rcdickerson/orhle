{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.FunImp
  ( AExp(..)
  , BExp(..)
  , CallId
  , CollectLoopHeadStates(..)
  , DefaultFunImpEvalContext(..)
  , Embeddable(..)
  , Fuel(..)
  , FuelTank(..)
  , FunImpl(..)
  , FunImplEnv
  , FunImplLookup(..)
  , FunImpProgram
  , ImpAsgn(..)
  , ImpBackwardPT(..)
  , ImpCall(..)
  , ImpExpr(..)
  , ImpForwardPT(..)
  , ImpIf(..)
  , ImpPieContext(..) -- TODO: This should live in the PIE module?
  , ImpPieContextProvider(..)
  , ImpSkip(..)
  , ImpSeq(..)
  , ImpStep
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , LoopHeadStates
  , MapImpType(..)
  , Name(..)
  , SplitOnBExp(..)
  , TransformMetadata(..)
  , eval
  , impAsgn
  , impCall
  , impIf
  , impSeq
  , impSkip
  , impWhile
  , impWhileWithMeta
  , inject
  , mapLoopHeadStates
  , populateLoopIds
  , prettyArgs
  , prettyAssignees
  , repopulateLoopIds
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Evaluation
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Language.Imp
import Ceili.Literal
import Ceili.Name
import Ceili.StatePredicate
import Control.Monad ( foldM )
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prettyprinter


------------------------------
-- Function Implementations --
------------------------------

data FunImpl e = FunImpl { fimpl_params  :: [Name]
                         , fimpl_body    :: e
                         , fimpl_returns :: [Name]
                         } deriving (Eq, Show, Functor)

instance CollectableNames e => CollectableNames (FunImpl e) where
  namesIn (FunImpl params body returns) =
    Set.unions [ Set.fromList params
               , namesIn body
               , Set.fromList returns ]

instance MappableNames e => MappableNames (FunImpl e) where
  mapNames f (FunImpl params body returns) =
    FunImpl (map f params) (mapNames f body) (map f returns)

instance FreshableNames e => FreshableNames (FunImpl e) where
  freshen (FunImpl params body returns) = do
    params'  <- freshen params
    body'    <- freshen body
    returns' <- freshen returns
    return $ FunImpl params' body' returns'

instance CollectableLiterals e t => CollectableLiterals (FunImpl e) t where
  litsIn (FunImpl _ body _) = litsIn body

instance TransformMetadata m e t => TransformMetadata m (FunImpl e) t where
  transformMetadata (FunImpl params body rets) f = do
    body' <- transformMetadata body f
    return $ FunImpl params body' rets

------------------------------------------
-- Function Implementation Environments --
------------------------------------------

type FunImplEnv e = Map Handle (FunImpl e)

class FunImplLookup a e where
  lookupFunImpl :: a -> Handle -> Ceili (FunImpl e)

instance FunImplLookup (FunImplEnv e) e where
  lookupFunImpl env name = case Map.lookup name env of
      Nothing   -> throwError $ "No implementation for " ++ name
      Just impl -> return impl

instance CollectableNames e => CollectableNames (FunImplEnv e) where
  namesIn = namesIn . Map.elems


--------------------
-- Function Calls --
--------------------

type CallId = String

data ImpCall t e = ImpCall CallId [AExp t] [Name]
  deriving (Eq, Ord, Show, Functor)

instance CollectableNames (ImpCall t e) where
  namesIn (ImpCall _ args assignees) =
    Set.union (namesIn args) (namesIn assignees)

instance FreshableNames (ImpCall t e) where
  freshen (ImpCall cid args assignees) = do
    args'      <- freshen args
    assignees' <- freshen assignees
    return $ ImpCall cid args' assignees'

instance MappableNames (ImpCall t e) where
  mapNames f (ImpCall cid args assignees) =
    ImpCall cid (map (mapNames f) args) (map f assignees)

instance Ord t => CollectableLiterals (ImpCall t e) t where
  litsIn (ImpCall _ args _) = litsIn args

instance Monad m => TransformMetadata m (ImpCall t e) t where
  transformMetadata call _ = return call

instance MapImpType t t' (ImpCall t e) (ImpCall t' e') where
  mapImpType f (ImpCall cid args assignees) = ImpCall cid (map (fmap f) args) assignees


---------------------
-- FunImp Language --
---------------------

type FunImpProgram t = ImpExpr t ( ImpCall t
                               :+: ImpSkip t
                               :+: ImpAsgn t
                               :+: ImpSeq t
                               :+: ImpIf t
                               :+: ImpWhile t)

instance CollectableNames (FunImpProgram t) where
  namesIn (In f) = namesIn f

instance MappableNames (FunImpProgram t) where
  mapNames func (In f) = In $ mapNames func f

instance FreshableNames (FunImpProgram t) where
  freshen (In f) = return . In =<< freshen f

instance Ord t => CollectableLiterals (FunImpProgram t) t where
  litsIn (In f) = litsIn f

instance Monad m => TransformMetadata m (FunImpProgram t) t where
  transformMetadata (In prog) f = do prog' <- transformMetadata prog f; return $ In prog'

instance MapImpType t t' (FunImpProgram t) (FunImpProgram t') where
  mapImpType f (In p) = In $ mapImpType f p

impCall :: (ImpCall t :<: f) => CallId -> [AExp t] -> [Name] -> ImpExpr t f
impCall cid args assignees = inject $ ImpCall cid args assignees


-----------------
-- Interpreter --
-----------------

data DefaultFunImpEvalContext e = DefaultFunImpEvalContext { dfiec_impls :: FunImplEnv e
                                                           , dfiec_fuel  :: Fuel
                                                           }
instance FunImplLookup (DefaultFunImpEvalContext e) e where
  lookupFunImpl = lookupFunImpl . dfiec_impls
instance FuelTank (DefaultFunImpEvalContext e) where
  getFuel = getFuel . dfiec_fuel
  setFuel (DefaultFunImpEvalContext impls _) fuel = DefaultFunImpEvalContext impls fuel


getOrFail :: ProgState a -> Name -> Ceili a
getOrFail state name = case Map.lookup name state of
  Nothing  -> throwError $ "No program state mapping for " ++ show name
  Just val -> return val

instance ( FunImplLookup c e
         , SplitOnBExp t
         , Evaluable c t (AExp t) t
         , Evaluable c t e (ImpStep t)
         ) => Evaluable c t (ImpCall t e) (ImpStep t) where
  eval ctx st (ImpCall cid args assignees) = do
    impl <- lookupFunImpl ctx cid :: Ceili (FunImpl e)
    let evalArg = eval @c @t @(AExp t) @t ctx st
    let eargs = map evalArg args
    let inputSt = Map.fromList $ zip (fimpl_params impl) eargs
    let setAssignments outSt = do
          retVals <- mapM (getOrFail outSt) (fimpl_returns impl)
          let assgns = Map.fromList $ zip assignees retVals
          return $ Map.union assgns st
    mapM setAssignments =<< eval ctx inputSt (fimpl_body impl)

-- TODO: Evaluating a function call should cost fuel to prevent infinite recursion.

instance ( FuelTank c
         , FunImplLookup c (FunImpProgram t)
         , SplitOnBExp t
         , Evaluable c t (AExp t) t
         )
        => Evaluable c t (FunImpProgram t) (ImpStep t) where
  eval ctx st (In program) = eval ctx st program


----------------------
-- Loop Head States --
----------------------

instance ( FunImplLookup c e
         , Evaluable c t (AExp t) t
         , Evaluable c t e (ImpStep t)
         ) => CollectLoopHeadStates c (ImpCall t e) t where
  collectLoopHeadStates _ _ _ = return Map.empty

instance ( Ord t
         , FuelTank c
         , FunImplLookup c (FunImpProgram t)
         , SplitOnBExp t
         , Evaluable c t (AExp t) t
         ) => CollectLoopHeadStates c (FunImpProgram t) t where
  collectLoopHeadStates ctx sts (In f) = collectLoopHeadStates ctx sts f


-- TODO: PTSes don't handle recursion. Add detection to fail gracefully instead of
-- spinning forever.


--------------------
-- Pretty Printer --
--------------------

instance Pretty t => Pretty (ImpCall t e) where
  pretty (ImpCall callId args assignees) =
    prettyAssignees assignees <+> pretty ":=" <+> pretty callId <> prettyArgs args

prettyAssignees :: Pretty a => [a] -> Doc ann
prettyAssignees assignees =
  case assignees of
    []     -> pretty "??"
    (x:[]) -> pretty x
    _      -> encloseSep lparen rparen comma (map pretty assignees)

prettyArgs :: Pretty a => [a] -> Doc ann
prettyArgs args =
  case args of
    []     -> pretty "()"
    (x:[]) -> parens $ pretty x
    _      -> encloseSep lparen rparen comma (map pretty args)


instance Pretty t => Pretty (FunImpProgram t) where
  pretty (In p) = pretty p


----------------------------------
-- Backward Predicate Transform --
----------------------------------

instance ( Embeddable Integer t
         , Ord t
         , ValidCheckable t
         , AssertionParseable t
         , Pretty t
         , FunImplLookup c (FunImpProgram t)
         , StatePredicate (Assertion t) t
         , ImpPieContextProvider c t
         ) => ImpBackwardPT c (FunImpProgram t) t where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post

instance ( FunImplLookup c e
         , ImpBackwardPT c e t
         , FreshableNames e
         ) => ImpBackwardPT c (ImpCall t e) t where
  impBackwardPT ctx (ImpCall cid args assignees) post = do
    (impl :: FunImpl e) <- lookupFunImpl ctx cid
    FunImpl params body returns <- envFreshen impl
    post' <- assignBackward ctx assignees (map AVar returns) post
    wp    <- impBackwardPT ctx body post'
    assignBackward ctx params args wp

assignBackward :: c -> [Name] -> [AExp t] -> Assertion t -> Ceili (Assertion t)
assignBackward ctx params args post =
  if length params /= length args
    then throwError "Different number of params and args"
    else do
      let doAsgn post' (a1, a2) = impBackwardPT ctx (ImpAsgn a1 a2) post'
      foldM doAsgn post $ zip params args


----------------------------------
-- Forward Predicate Transform --
----------------------------------

instance ( Embeddable Integer t
         , Ord t
         , ValidCheckable t
         , Pretty t
         , AssertionParseable t
         , FunImplLookup c (FunImpProgram t)
         , CollectableNames (FunImpProgram t)
         , StatePredicate (Assertion t) t
         ) => ImpForwardPT c (FunImpProgram t) t where
  impForwardPT ctx (In f) pre = impForwardPT ctx f pre

instance (FunImplLookup c e, ImpForwardPT c e t, FreshableNames e) => ImpForwardPT c (ImpCall t e) t where
  impForwardPT ctx (ImpCall cid args assignees) pre = do
    (impl :: FunImpl e) <- lookupFunImpl ctx cid
    FunImpl params body returns <- envFreshen impl
    pre' <- assignForward ctx params args pre
    sp   <- impForwardPT ctx body pre'
    assignForward ctx assignees (map AVar returns) sp

assignForward :: c -> [Name] -> [AExp t] -> Assertion t -> Ceili (Assertion t)
assignForward impls params args pre =
  if length params /= length args
    then throwError "Different number of params and args"
    else do
      let doAsgn pre' (a1, a2) = impForwardPT impls (ImpAsgn a1 a2) pre'
      foldM doAsgn pre $ zip params args
