{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.Imp
  ( AExp(..)
  , BExp(..)
  , CollectLoopHeadStates(..)
  , Embeddable(..)
  , Fuel(..)
  , FuelTank(..)
  , ImpAsgn(..)
  , ImpBackwardPT(..)
  , ImpExpr(..)
  , ImpForwardPT(..)
  , ImpIf(..)
  , ImpPieContext(..) -- TODO: Move to PIE module?
  , ImpPieContextProvider(..)
  , ImpProgram
  , ImpSeq(..)
  , ImpSkip(..)
  , ImpStep
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , IterStateMap
  , LoopHeadStates
  , MapImpType(..)
  , Name(..)
  , ProgState
  , SplitOnBExp(..)
  , TransformMetadata(..)
  , emptyWhileMetadata
  , eval
  , impAsgn
  , impIf
  , impSeq
  , impSeqIfNeeded
  , impSkip
  , impWhile
  , impWhileWithMeta
  , inject
  , mapLoopHeadStates
  , populateLoopIds
  , repopulateLoopIds
  , unionIterStates
  ) where

import Ceili.Assertion.AssertionLanguage ( Assertion)
import Ceili.Assertion.AssertionParser ( AssertionParseable )
import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Evaluation
import qualified Ceili.FeatureLearning.LinearInequalities as LI
import qualified Ceili.FeatureLearning.Pie as Pie
import qualified Ceili.InvariantInference.Houdini as Houdini
import qualified Ceili.InvariantInference.LoopInvGen as Lig
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Literal
import Ceili.Name
import Ceili.ProgState
import Ceili.StatePredicate
import Data.UUID
import qualified Data.UUID.V4 as UUID
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter


--------------
-- Language --
--------------

data ImpExpr t f = In (f (ImpExpr t f))

instance Eq (f (ImpExpr t f)) => Eq (ImpExpr t f) where
  (In f1) == (In f2) = f1 == f2

instance Show (f (ImpExpr t f)) => Show (ImpExpr t f) where
  show (In f) = show f

data ImpSkip t e = ImpSkip
  deriving (Eq, Ord, Show, Functor)

data ImpAsgn t e = ImpAsgn Name (AExp t)
  deriving (Eq, Ord, Show, Functor)

data ImpSeq t e = ImpSeq [e]
  deriving (Eq, Ord, Show, Functor)

data ImpIf t e = ImpIf (BExp t) e e
  deriving (Eq, Ord, Show, Functor)

data ImpWhile t e = ImpWhile { impWhile_cond :: BExp t
                             , impWhile_body :: e
                             , impWhile_meta :: ImpWhileMetadata t
                             }
  deriving (Eq, Ord, Show, Functor)

type ImpProgram t = ImpExpr t ( ImpSkip t
                            :+: ImpAsgn t
                            :+: ImpSeq t
                            :+: ImpIf t
                            :+: ImpWhile t )

-----------------------
-- ImpWhile Metadata --
-----------------------

data ImpWhileMetadata t =
  ImpWhileMetadata { iwm_id        :: Maybe UUID
                   , iwm_invariant :: Maybe (Assertion t)
                   , iwm_measure   :: Maybe (A.Arith t)
                   } deriving (Eq, Ord, Show, Functor)

emptyWhileMetadata :: ImpWhileMetadata t
emptyWhileMetadata = ImpWhileMetadata Nothing Nothing Nothing

instance MappableNames (ImpWhileMetadata t) where
  mapNames f (ImpWhileMetadata loopId mInvar mMeasure) =
    let
      mInvar'   = do invar   <- mInvar;   return $ mapNames f invar
      mMeasure' = do measure <- mMeasure; return $ mapNames f measure
    in ImpWhileMetadata loopId mInvar' mMeasure'

instance FreshableNames (ImpWhileMetadata t) where
  freshen (ImpWhileMetadata loopId invar measure) = do
    invar'   <- freshen invar
    measure' <- freshen measure
    return $ ImpWhileMetadata loopId invar' measure'

class Monad m => TransformMetadata m a t where
  transformMetadata :: a -> (ImpWhileMetadata t -> m (ImpWhileMetadata t)) -> m a
instance Monad m => TransformMetadata m (ImpSkip t e) t where
  transformMetadata skip _ = return skip
instance Monad m => TransformMetadata m (ImpAsgn t e) t where
  transformMetadata asgn _ = return asgn
instance TransformMetadata m e t => TransformMetadata m (ImpSeq t e) t where
  transformMetadata (ImpSeq stmts) f = do
    stmts' <- sequence $ map (\s -> transformMetadata s f) stmts
    return $ ImpSeq stmts'
instance TransformMetadata m e t => TransformMetadata m (ImpIf t e) t where
  transformMetadata (ImpIf cond tbranch fbranch) f = do
    tbranch' <- transformMetadata tbranch f
    fbranch' <- transformMetadata fbranch f
    return $ ImpIf cond tbranch' fbranch'
instance TransformMetadata m e t => TransformMetadata m (ImpWhile t e) t where
  transformMetadata (ImpWhile cond body meta) f = do
    body' <- transformMetadata body f
    meta' <- f meta
    return $ ImpWhile cond body' meta'
instance ( TransformMetadata m (f e) t
         , TransformMetadata m (g e) t
         ) => TransformMetadata m ((f :+: g) e) t where
  transformMetadata (Inl f) func = do f' <- transformMetadata f func; return $ Inl f'
  transformMetadata (Inr g) func = do g' <- transformMetadata g func; return $ Inr g'
instance Monad m => TransformMetadata m (ImpProgram t) t where
  transformMetadata (In prog) func = do prog' <- transformMetadata prog func; return $ In prog'

populateLoopIds :: forall p t. TransformMetadata IO p t => p -> IO p
populateLoopIds prog = transformMetadata @IO @p @t prog updateLoopId
  where
    updateLoopId :: ImpWhileMetadata t -> IO (ImpWhileMetadata t)
    updateLoopId (ImpWhileMetadata uuid invar meas) = do
      uuid' <- case uuid of
        Nothing -> UUID.nextRandom >>= return . Just
        Just _  -> return uuid
      return $ ImpWhileMetadata uuid' invar meas

repopulateLoopIds :: forall p t. TransformMetadata IO p t => p -> IO p
repopulateLoopIds prog = transformMetadata @IO @p @t prog overwriteLoopId
  where
    overwriteLoopId :: ImpWhileMetadata t -> IO (ImpWhileMetadata t)
    overwriteLoopId (ImpWhileMetadata _ invar meas) = do
      uuid  <- UUID.nextRandom
      return $ ImpWhileMetadata (Just uuid) invar meas


------------------------
-- Smart Constructors --
------------------------

inject :: (g t :<: f) => g t (ImpExpr t f) -> ImpExpr t f
inject = In . inj

impSkip :: (ImpSkip t :<: f) => ImpExpr t f
impSkip = inject ImpSkip

impAsgn :: (ImpAsgn t :<: f) => Name -> AExp t -> ImpExpr t f
impAsgn lhs rhs = inject $ ImpAsgn lhs rhs

impSeq :: (ImpSeq t :<: f) => [ImpExpr t f] -> ImpExpr t f
impSeq stmts = inject $ ImpSeq stmts

impSeqIfNeeded :: (ImpSkip t :<: f, ImpSeq t :<: f) => [ImpExpr t f] -> ImpExpr t f
impSeqIfNeeded stmts = case stmts of
  []   -> impSkip
  s:[] -> s
  ss   -> impSeq ss

impIf :: (ImpIf t :<: f) => BExp t -> ImpExpr t f -> ImpExpr t f -> ImpExpr t f
impIf cond tBranch eBranch = inject $ ImpIf cond tBranch eBranch

impWhile :: (ImpWhile t :<: f) => BExp t -> ImpExpr t f -> ImpExpr t f
impWhile cond body = inject $ ImpWhile cond body emptyWhileMetadata

impWhileWithMeta :: (ImpWhile t :<: f) => BExp t -> ImpExpr t f -> ImpWhileMetadata t -> ImpExpr t f
impWhileWithMeta cond body meta = inject $ ImpWhile cond body meta


----------------------
-- CollectableNames --
----------------------

instance CollectableNames (ImpSkip t e) where
  namesIn ImpSkip = Set.empty

instance CollectableNames (ImpAsgn t e) where
  namesIn (ImpAsgn var aexp) = Set.insert var $ namesIn aexp

instance CollectableNames e => CollectableNames (ImpSeq t e) where
  namesIn (ImpSeq stmts) = namesIn stmts

instance CollectableNames e => CollectableNames (ImpIf t e) where
  namesIn (ImpIf cond bThen bElse) = Set.unions
    [namesIn cond, namesIn bThen, namesIn bElse]

instance CollectableNames e => CollectableNames (ImpWhile t e) where
  namesIn (ImpWhile cond body _) = Set.union (namesIn cond) (namesIn body)

instance CollectableNames (ImpProgram t)
  where namesIn (In p) = namesIn p


-------------------
-- MappableNames --
-------------------

instance MappableNames (ImpSkip t e) where
  mapNames _ ImpSkip = ImpSkip

instance MappableNames (ImpAsgn t e) where
  mapNames f (ImpAsgn var aexp) = ImpAsgn (f var) (mapNames f aexp)

instance MappableNames e => MappableNames (ImpSeq t e) where
  mapNames f (ImpSeq stmts) = ImpSeq $ mapNames f stmts

instance MappableNames e => MappableNames (ImpIf t e) where
  mapNames f (ImpIf c t e) = ImpIf (mapNames f c) (mapNames f t) (mapNames f e)

instance MappableNames e => MappableNames (ImpWhile t e) where
    mapNames f (ImpWhile cond body meta) =
      ImpWhile (mapNames f cond) (mapNames f body) (mapNames f meta)

instance MappableNames (ImpProgram t)
  where mapNames f (In p) = In $ mapNames f p


--------------------
-- FreshableNames --
--------------------

instance FreshableNames (ImpSkip t e) where
  freshen ImpSkip = return ImpSkip

instance FreshableNames (ImpAsgn t e) where
  freshen (ImpAsgn var aexp) = do
    var'  <- freshen var
    aexp' <- freshen aexp
    return $ ImpAsgn var' aexp'

instance FreshableNames e => FreshableNames (ImpSeq t e) where
  freshen (ImpSeq stmts) = return . ImpSeq =<< freshen stmts

instance FreshableNames e => FreshableNames (ImpIf t e) where
  freshen (ImpIf c t e) = do
    c' <- freshen c
    t' <- freshen t
    e' <- freshen e
    return $ ImpIf c' t' e'

instance FreshableNames e => FreshableNames (ImpWhile t e) where
  freshen (ImpWhile cond body meta) = do
    cond' <- freshen cond
    body' <- freshen body
    meta' <- freshen meta
    return $ ImpWhile cond' body' meta'

instance FreshableNames (ImpProgram t) where
  freshen (In p) = return . In =<< freshen p


-------------------------
-- CollectableLiterals --
-------------------------

instance CollectableLiterals (ImpSkip t e) t where
  litsIn ImpSkip = Set.empty

instance Ord t => CollectableLiterals (ImpAsgn t e) t where
  litsIn (ImpAsgn _ rhs) = litsIn rhs

instance (Ord t, CollectableLiterals e t) => CollectableLiterals (ImpSeq t e) t where
  litsIn (ImpSeq stmts) = litsIn stmts

instance (Ord t, CollectableLiterals e t) => CollectableLiterals (ImpIf t e) t where
  litsIn (ImpIf cond tBranch eBranch) = Set.unions
    [litsIn cond, litsIn tBranch, litsIn eBranch]

instance (Ord t, CollectableLiterals e t) => CollectableLiterals (ImpWhile t e) t where
  litsIn (ImpWhile cond body _) = Set.union (litsIn cond) (litsIn body)

instance Ord t => CollectableLiterals (ImpProgram t) t where
  litsIn (In f) = litsIn f


---------------
-- Map Types --
---------------

class MapImpType t t' f f' where
  mapImpType :: (t -> t') -> f -> f'

instance MapImpType t t' (ImpSkip t e) (ImpSkip t' e') where
  mapImpType _ _ = ImpSkip

instance MapImpType t t' (ImpAsgn t e) (ImpAsgn t' e') where
  mapImpType f (ImpAsgn lhs rhs) = ImpAsgn lhs (fmap f rhs)

instance MapImpType t t' e e' => MapImpType t t' (ImpSeq t e) (ImpSeq t' e') where
  mapImpType f (ImpSeq stmts) = ImpSeq $ map (mapImpType f) stmts

instance MapImpType t t' e e' => MapImpType t t' (ImpIf t e) (ImpIf t' e') where
  mapImpType f (ImpIf cond tbranch ebranch) = ImpIf (fmap f cond)
                                                    (mapImpType f tbranch)
                                                    (mapImpType f ebranch)

instance MapImpType t t' e e' => MapImpType t t' (ImpWhile t e) (ImpWhile t' e') where
  mapImpType f (ImpWhile cond body meta) = ImpWhile (fmap f cond)
                                                    (mapImpType f body)
                                                    (fmap f meta)

instance ( MapImpType t t' (f e) (f' e')
         , MapImpType t t' (g e) (g' e')
         ) => MapImpType t t' ((f :+: g) e) ((f' :+: g') e') where
  mapImpType func (Inl f) = Inl $ mapImpType func f
  mapImpType func (Inr g) = Inr $ mapImpType func g

instance MapImpType t t' (ImpProgram t) (ImpProgram t') where
  mapImpType f (In p) = In $ mapImpType f p


-----------------
-- Interpreter --
-----------------

type ImpStep t = Ceili [ProgState t]

data Fuel = Fuel Int
          | InfiniteFuel

class FuelTank t where
  getFuel :: t -> Fuel
  setFuel :: t -> Fuel -> t

instance FuelTank Fuel where
  getFuel   = id
  setFuel _ = id

class SplitOnBExp t where
  splitOnBExp :: BExp t -> ProgState t -> Ceili ( Maybe (ProgState t)
                                                , Maybe (ProgState t) )

instance SplitOnBExp Integer where
  splitOnBExp bexp st = return $ if eval () st bexp
                                 then (Nothing, Just st)
                                 else (Just st, Nothing)

partitionOnBExp :: SplitOnBExp t => BExp t -> [ProgState t] -> Ceili ([ProgState t], [ProgState t])
partitionOnBExp bexp sts = do
  splitSts <- mapM (splitOnBExp bexp) sts
  let foldSts (mFSt, mTSt) (fSts, tSts) =
        case (mFSt, mTSt) of
          (Nothing , Nothing)  -> (fSts    , tSts)
          (Just fSt, Nothing)  -> (fSt:fSts, tSts)
          (Nothing , Just tSt) -> (fSts    , tSt:tSts)
          (Just fSt, Just tSt) -> (fSt:fSts, tSt:tSts)
  return $ foldr foldSts ([], []) splitSts

decrementFuel :: (FuelTank f) => f -> f
decrementFuel fuel =
  case getFuel fuel of
    Fuel n | n > 0 -> setFuel fuel $ Fuel (n - 1)
    _ -> fuel

instance Evaluable c t (ImpSkip t e) (ImpStep t) where
  eval _ st _ = return [st]

instance (Evaluable c t (AExp t) t) => Evaluable c t (ImpAsgn t e) (ImpStep t) where
  eval ctx st (ImpAsgn var aexp) = return $ [Map.insert var (eval ctx st aexp) st]

instance Evaluable c t e (ImpStep t) => Evaluable c t (ImpSeq t e) (ImpStep t) where
  eval = evalSeq

evalSeq :: Evaluable c t e (ImpStep t)
        => c -> ProgState t -> (ImpSeq t e) -> ImpStep t
evalSeq ctx st (ImpSeq stmts) =
  case stmts of
    [] -> return [st]
    (stmt:rest) -> do
      mSts' <- eval ctx st stmt
      case mSts' of
        [] -> return []
        sts' -> return . concat =<< mapM (\s -> evalSeq ctx s (ImpSeq rest)) sts'

instance ( SplitOnBExp t, Evaluable c t e (ImpStep t) )
        => Evaluable c t (ImpIf t e) (ImpStep t) where
  eval ctx st (ImpIf cond t f) = do
    (mFalseSt, mTrueSt) <- splitOnBExp cond st
    falseSts <- case mFalseSt of
                  Nothing  -> return []
                  Just fSt -> eval ctx fSt f
    trueSts  <- case mTrueSt of
                  Nothing  -> return []
                  Just tSt -> eval ctx tSt t
    return $ falseSts ++ trueSts

instance ( FuelTank c
         , SplitOnBExp t
         , Evaluable c t e (ImpStep t)
         )
        => Evaluable c t (ImpWhile t e) (ImpStep t) where
  eval = evalWhile

evalWhile :: forall c t e.
             ( FuelTank c
             , SplitOnBExp t
             , Evaluable c t e (ImpStep t)
             )
          => c
          -> ProgState t
          -> (ImpWhile t e)
          -> ImpStep t
evalWhile ctx st loop@(ImpWhile cond body meta) = do
  (mFalseSt, mTrueSt) <- splitOnBExp cond st
  let falseSts = case mFalseSt of
                   Nothing  -> []
                   Just fSt -> [fSt]
  trueSts <- case mTrueSt of
               Nothing  -> return []
               Just tSt ->
                 let ctx' = decrementFuel ctx
                 in case (getFuel ctx') of
                      Fuel n | n <= 0 -> log_e "Evaluation ran out of fuel" >> return []
                      _ -> do
                        sts' <- eval ctx' tSt body :: ImpStep t
                        return . concat =<< mapM (\s -> evalWhile ctx' s loop) sts'
  return $ falseSts ++ trueSts

instance ( FuelTank c
         , Evaluable c t (AExp t) t
         , SplitOnBExp t
         )
        => Evaluable c t (ImpProgram t) (ImpStep t) where
  eval ctx st (In program) = eval ctx st program


----------------------
-- Loop Head States --
----------------------

type LoopHeadStates t = Map UUID (IterStateMap t)
type IterStateMap t   = Map Int (Set (ProgState t))

mapLoopHeadStates :: Ord b => (a -> b) -> LoopHeadStates a -> LoopHeadStates b
mapLoopHeadStates = Map.map . Map.map . Set.map . Map.map

class CollectLoopHeadStates ctx expr t where
  collectLoopHeadStates :: ctx -> [ProgState t] -> expr -> Ceili (LoopHeadStates t)

instance CollectLoopHeadStates c (ImpSkip t e) t where
  collectLoopHeadStates _ _ _ = return Map.empty

instance Evaluable c t (AExp t) t => CollectLoopHeadStates c (ImpAsgn t e) t where
  collectLoopHeadStates _ _ _ = return Map.empty

instance ( Ord t
         , CollectLoopHeadStates c e t
         , SplitOnBExp t
         , Evaluable c t e (ImpStep t)
         )
         => CollectLoopHeadStates c (ImpSeq t e) t where
  collectLoopHeadStates = seqHeadStates

seqHeadStates :: ( Ord t
                 , CollectLoopHeadStates c e t
                 , SplitOnBExp t
                 , Evaluable c t e (ImpStep t))
              => c
              -> [ProgState t]
              -> ImpSeq t e
              -> Ceili (LoopHeadStates t)
seqHeadStates ctx sts (ImpSeq stmts) =
  case stmts of
    [] -> return Map.empty
    stmt:rest -> do
      stmtHeads <- collectLoopHeadStates ctx sts stmt
      sts' <- return . concat =<< mapM (\s -> eval ctx s stmt) sts
      restHeads <- seqHeadStates ctx sts' (ImpSeq rest)
      return $ unionLoopHeadStates stmtHeads restHeads

instance ( Ord t
         , SplitOnBExp t
         , CollectLoopHeadStates c e t
         )
         => CollectLoopHeadStates c (ImpIf t e) t where
  collectLoopHeadStates ctx sts (ImpIf cond t f) = do
    (tStates, fStates) <- partitionOnBExp cond sts
    tHeads <- collectLoopHeadStates ctx tStates t
    fHeads <- collectLoopHeadStates ctx fStates f
    return $ unionLoopHeadStates tHeads fHeads

instance ( FuelTank c
         , Ord t
         , SplitOnBExp t
         , CollectLoopHeadStates c e t
         , Evaluable c t e (ImpStep t)
         )
         => CollectLoopHeadStates c (ImpWhile t e) t where
  collectLoopHeadStates ctx sts loop@(ImpWhile cond body meta) = do
    loopId <- case iwm_id meta of
      Nothing  -> throwError "Loop missing ID."
      Just lid -> return lid
    loopStates <- iterateLoopStates ctx 0 sts loop
    (_, trueSts) <- partitionOnBExp cond sts
    bodyStates <- collectLoopHeadStates ctx trueSts body
    return $ unionLoopHeadStates (Map.singleton loopId loopStates) bodyStates

iterateLoopStates :: ( FuelTank c
                     , Ord t
                     , SplitOnBExp t
                     , Evaluable c t e (ImpStep t)
                     )
                  => c
                  -> Int
                  -> [ProgState t]
                  -> (ImpWhile t e)
                  -> Ceili (IterStateMap t)
iterateLoopStates ctx iterNum sts loop@(ImpWhile cond body _) = do
  let thisIter = Map.singleton iterNum (Set.fromList sts)
  case getFuel ctx of
    Fuel 0 -> return thisIter
    _ -> do
      (_, trueSts) <- partitionOnBExp cond sts
      case trueSts of
        [] -> return thisIter
        _  -> do
          nextSts <- return . concat =<< mapM (\s -> eval ctx s body) trueSts
          rest <- iterateLoopStates (decrementFuel ctx) (iterNum + 1) nextSts loop
          return $ unionIterStates thisIter rest

instance (CollectLoopHeadStates c (f e) t, CollectLoopHeadStates c (g e) t) =>
         CollectLoopHeadStates c ((f :+: g) e) t where
  collectLoopHeadStates ctx st (Inl f) = collectLoopHeadStates ctx st f
  collectLoopHeadStates ctx st (Inr g) = collectLoopHeadStates ctx st g

instance ( FuelTank c
         , Ord t
         , SplitOnBExp t
         , Evaluable c t (AExp t) t
         ) => CollectLoopHeadStates c (ImpProgram t) t where
  collectLoopHeadStates fuel sts (In f) = collectLoopHeadStates fuel sts f

unionLoopHeadStates :: Ord t => LoopHeadStates t -> LoopHeadStates t -> LoopHeadStates t
unionLoopHeadStates = Map.unionWith unionIterStates

unionIterStates :: Ord t => IterStateMap t -> IterStateMap t -> IterStateMap t
unionIterStates = Map.unionWith Set.union

mapIterMapNames :: Ord t => (Name -> Name) -> IterStateMap t -> IterStateMap t
mapIterMapNames f iterMap = let
  assocList = Map.assocs iterMap
  mapAssoc (k, v) = (k, mapNames f v)
  in Map.fromAscList $ map mapAssoc assocList

freshenIterMapNames :: Ord t => IterStateMap t -> Freshener (IterStateMap t)
freshenIterMapNames iterMap = do
  let assocList = Map.assocs iterMap
  let freshenAssoc (k, v) = do v' <- freshen v; return (k, v')
  assocList' <- sequence $ map freshenAssoc assocList
  return $ Map.fromAscList assocList'


--------------------
-- Pretty Printer --
--------------------

instance Pretty (ImpSkip t e) where
  pretty _ = pretty "skip"

instance Pretty t => Pretty (ImpAsgn t e) where
  pretty (ImpAsgn lhs rhs) = pretty lhs <+> pretty ":=" <+> pretty rhs

instance Pretty e => Pretty (ImpSeq t e) where
  pretty (ImpSeq stmts) = vsep $ map (\stmt -> pretty stmt <> semi) stmts

instance (Pretty t, Pretty e) => Pretty (ImpIf t e) where
  pretty (ImpIf cond tBranch eBranch) =
    pretty "if" <> softline <> pretty cond
    <> softline <> pretty "then"
    <> line <> (indent 2 $ pretty tBranch)
    <> line <> pretty "else"
    <> line <> (indent 2 $ pretty eBranch)
    <> line <> pretty "endif"

instance (Pretty t, Pretty e) => Pretty (ImpWhile t e) where
  pretty (ImpWhile cond body _) =
    pretty "while" <> softline <> pretty cond
    <> line <> (indent 2 $ pretty body)
    <> line <> pretty "end"

instance Pretty t => Pretty (ImpProgram t) where
  pretty (In p) = pretty p


--------------------------------------------
-- Backward Predicate Transform (Partial) --
--------------------------------------------

class ImpPieContextProvider ctx t where
  impPieCtx :: ctx -> ImpPieContext t

data ImpPieContext t = ImpPieContext
  { pc_loopHeadStates   :: LoopHeadStates t
  , pc_programNames     :: Set Name
  , pc_programLits      :: Set t
  }

instance ImpPieContextProvider (ImpPieContext t) t where
  impPieCtx = id

class ImpBackwardPT ctx expr t where
  impBackwardPT :: ctx -> expr -> Assertion t -> Ceili (Assertion t)

instance ImpBackwardPT c (ImpSkip t e) t where
  impBackwardPT _ ImpSkip post = return post

instance ImpBackwardPT c (ImpAsgn t e) t where
  impBackwardPT _ (ImpAsgn lhs rhs) post =
    return $ A.subArith lhs
                        (aexpToArith rhs)
                        post

instance ImpBackwardPT c e t => ImpBackwardPT c (ImpSeq t e) t where
  impBackwardPT = impSeqBackwardPT

impSeqBackwardPT :: (ImpBackwardPT c e t)
                 => c
                 -> (ImpSeq t e)
                 -> Assertion t
                 -> Ceili (Assertion t)
impSeqBackwardPT ctx (ImpSeq stmts) post =
  case stmts of
    [] -> return post
    (s:ss) -> do
      post' <- impSeqBackwardPT ctx (ImpSeq ss) post
      impBackwardPT ctx s post'

instance ImpBackwardPT c e t => ImpBackwardPT c (ImpIf t e) t where
  impBackwardPT ctx (ImpIf condB tBranch eBranch) post = do
    wpT <- impBackwardPT ctx tBranch post
    wpE <- impBackwardPT ctx eBranch post
    let cond   = bexpToAssertion condB
        ncond  = A.Not $ cond
    return $ A.And [A.Imp cond wpT, A.Imp ncond wpE]

instance ( Embeddable Integer t
         , Ord t
         , ValidCheckable t
         , Pretty t
         , AssertionParseable t
         , CollectableNames e
         , StatePredicate (Assertion t) t
         , ImpPieContextProvider c t
         , ImpBackwardPT c e t
         )
         => ImpBackwardPT c (ImpWhile t e) t where
  impBackwardPT ctx loop@(ImpWhile condB body _) post = let
    cond          = bexpToAssertion condB
    varSet        = Set.unions [namesIn condB, namesIn body]
    vars          = Set.toList varSet
    freshMapping  = snd $ buildFreshMap (buildFreshIds vars) vars
    (orig, fresh) = unzip $ Map.toList freshMapping
    freshen       = substituteAll orig fresh
    qNames        = Set.toList $ namesIn fresh
    in do
      mInv <- getLoopInvariant ctx loop post
      inv <- case mInv of
               Nothing -> do
                 log_i "Unable to find or infer loop invariant, proceding with False."
                 return A.AFalse
               Just i -> return i
      bodyWP <- impBackwardPT ctx body inv
      let loopWP = A.Forall qNames
                   (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      let endWP  = A.Forall qNames
                    (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
      return $ A.And [inv, loopWP, endWP]

getLoopInvariant :: ( Embeddable Integer t
                    , ValidCheckable t
                    , Ord t
                    , Pretty t
                    , AssertionParseable t
                    , StatePredicate (Assertion t) t
                    , ImpPieContextProvider ctx t
                    , ImpBackwardPT ctx e t )
                 => ctx
                 -> ImpWhile t e
                 -> Assertion t
                 -> Ceili (Maybe (Assertion t))
getLoopInvariant ctx (ImpWhile condB body meta) post =
  case iwm_invariant meta of
    Just i  -> return $ Just i
    Nothing -> do
      let pieCtx = impPieCtx ctx
      let mHeadStates = do
            loopId <- iwm_id meta
            Map.lookup loopId $ pc_loopHeadStates pieCtx
      case mHeadStates of
        Nothing -> return Nothing
        Just testStates -> do
          let conds = [bexpToAssertion condB]
          let names = pc_programNames pieCtx
          let lits  = pc_programLits  pieCtx
          let tests = Set.toList . Set.unions . Map.elems $ testStates
          let sepLearner _ bad good = do
                result <- Pie.pie Set.empty (LI.linearInequalities lits) bad good
                pure ((), result)
          Lig.loopInvGen ctx impBackwardPT conds body post tests (Lig.SeparatorLearner () sepLearner (pure . id))

instance (ImpBackwardPT c (f e) t, ImpBackwardPT c (g e) t) =>
         ImpBackwardPT c ((f :+: g) e) t where
  impBackwardPT ctx (Inl f) post = impBackwardPT ctx f post
  impBackwardPT ctx (Inr f) post = impBackwardPT ctx f post

instance ( Embeddable Integer t
         , ValidCheckable t
         , Pretty t
         , Ord t
         , AssertionParseable t
         , StatePredicate (Assertion t) t
         , ImpPieContextProvider c t
         ) => ImpBackwardPT c (ImpProgram t) t where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post


-------------------------------------------
-- Forward Predicate Transform (Partial) --
-------------------------------------------

class ImpForwardPT ctx expr t where
  impForwardPT :: ctx -> expr -> Assertion t -> Ceili (Assertion t)

instance ImpForwardPT c (ImpSkip t e) t where
  impForwardPT _ ImpSkip pre = return pre

instance ImpForwardPT c (ImpAsgn t e) t where
  impForwardPT _ (ImpAsgn lhs rhs) pre = do
    lhs' <- envFreshen lhs
    let
      subPre   = substitute lhs lhs' pre
      rhsArith = aexpToArith rhs
      subRhs   = A.subArith lhs (A.Var @t lhs') rhsArith
    return $ A.Exists [lhs'] $ A.And [A.Eq (A.Var lhs) subRhs, subPre]

instance ImpForwardPT c e t => ImpForwardPT c (ImpSeq t e) t where
  impForwardPT = impSeqForwardPT

impSeqForwardPT :: (ImpForwardPT c e t)
                 => c
                 -> (ImpSeq t e)
                 -> Assertion t
                 -> Ceili (Assertion t)
impSeqForwardPT ctx (ImpSeq stmts) pre =
  case stmts of
    []     -> return pre
    (s:ss) -> do
      pre' <- impForwardPT ctx s pre
      impSeqForwardPT ctx (ImpSeq ss) pre'

instance ImpForwardPT c e t => ImpForwardPT c (ImpIf t e) t where
  impForwardPT ctx (ImpIf b s1 s2) pre = do
    let cond = bexpToAssertion b
    postS1 <- impForwardPT ctx s1 (A.And [pre, cond])
    postS2 <- impForwardPT ctx s2 (A.And [pre, A.Not cond])
    return $ A.Or [postS1, postS2]

instance ( Embeddable Integer t
         , Ord t
         , ValidCheckable t
         , Pretty t
         , CollectableNames e
         , ImpForwardPT c e t )
        => ImpForwardPT c (ImpWhile t e) t where
  impForwardPT ctx (ImpWhile b body meta) pre = do
    let cond = bexpToAssertion b
    inv <- case (iwm_invariant meta) of
      Nothing  -> Houdini.infer (namesIn body) Set.empty 2 pre (impForwardPT ctx body) -- TODO: Lits
      Just inv -> return inv
    bodyInvSP <- impForwardPT ctx body inv
    log_d "Checking loop invariant verification conditions..."
    vcCheck <- checkValidB $ A.And [ A.Imp pre inv, A.Imp bodyInvSP inv ]
    if vcCheck
      then do log_d "Loop invariant verification conditions passed."
              return $ A.And [A.Not cond, inv]
      else throwError
           $ "Loop failed verification conditions. Invariant: " ++ show inv

instance (ImpForwardPT c (f e) t, ImpForwardPT c (g e) t) =>
         ImpForwardPT c ((f :+: g) e) t where
  impForwardPT ctx (Inl f) pre = impForwardPT ctx f pre
  impForwardPT ctx (Inr f) pre = impForwardPT ctx f pre

instance ( Embeddable Integer t
         , Ord t
         , ValidCheckable t
         , Pretty t
         ) => ImpForwardPT c (ImpProgram t) t where
  impForwardPT ctx (In f) pre = impForwardPT ctx f pre
