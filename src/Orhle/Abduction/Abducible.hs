module Orhle.Abduction.Abducible
  ( Abducible(..)
  , FreshVarMapping(..)
--  , fvmFlatten
--  , fvmFromAbducibles
  ) where

import           Control.Monad (foldM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Orhle.Imp
import qualified Orhle.SMT as SMT


data Abducible = Abducible
  { abdName   :: String
  , abdParams :: [Var]
  } deriving (Ord, Eq)

instance Show Abducible where
  show (Abducible name params) =
    "(" ++ name ++ ", params: " ++ (show params) ++ ")"

--------------------------------------------------------------------------------

data FreshVarMapping = FreshVarMapping
  { fvmOrigToFresh :: Map.Map Var Var
  , fvmFreshToOrig :: Map.Map Var Var
  , fvmOrigAbds    :: Set.Set Abducible
  , fvmFreshAbds   :: Set.Set Abducible
  }

fvmEmpty :: FreshVarMapping
fvmEmpty = FreshVarMapping Map.empty Map.empty Set.empty Set.empty

fvmInsert :: Abducible -> Abducible -> FreshVarMapping -> FreshVarMapping
fvmInsert abdOrig abdFresh fvm =
  FreshVarMapping origToFresh' freshToOrig' origAbds' freshAbds'
  where
    origToFresh' = foldr
                   (uncurry Map.insert)
                   (fvmOrigToFresh fvm)
                   (zip (abdParams abdOrig) (abdParams abdFresh))
    freshToOrig' = foldr
                   (uncurry Map.insert)
                   (fvmFreshToOrig fvm)
                   (zip (abdParams abdFresh) (abdParams abdOrig))
    origAbds'    = Set.insert abdOrig (fvmOrigAbds fvm)
    freshAbds'   = Set.insert abdFresh (fvmFreshAbds fvm)

-- fvmReplacementTerm :: FreshVarMapping -> Abducible -> SMT SMT.Expr
-- fvmReplacementTerm fvm abd = do
--   let varToAST = \v -> mkStringSymbol v >>= mkIntVar
--   abdVarASTs   <- sequence $ map varToAST $ abdParams abd
--   freshVarASTs <- sequence $ map varToAST $ freshVars
--   eqTerms      <- sequence $ map (uncurry mkEq) $ zip abdVarASTs freshVarASTs
--   mkAnd eqTerms
--     where freshVars = map (fvmOrigToFresh fvm Map.!) (abdParams abd)

-- fvmFromAbducibles :: [Abducible] -> SMT FreshVarMapping
-- fvmFromAbducibles abds = foldM insertAbd fvmEmpty abds
--   where
--     insertAbd fvm abd@(Abducible abdNameStr abdParamVars) = do
--         freshAbdParamASTs <- mkFreshIntVars abdParamVars
--         freshAbdParamVars <- mapM astToString freshAbdParamASTs
--         let freshAbd = Abducible abdNameStr freshAbdParamVars
--         return $ fvmInsert abd freshAbd fvm

-- fvmFlatten :: FreshVarMapping -> SMT.Expr -> SMT SMT.Expr
-- fvmFlatten fvm phi = foldM flattenAbd phi (fvmOrigAbds fvm)
--   where
--     flattenAbd :: SMT.Expr -> Abducible -> SMT SMT.Expr
--     flattenAbd phi' abd = do
--       abdAST      <- mkBoolVar =<< mkStringSymbol (abdName abd)
--       replacement <- fvmReplacementTerm fvm abd
--       substitute phi' [abdAST] [replacement]
