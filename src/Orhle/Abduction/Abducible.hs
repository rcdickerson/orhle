module Orhle.Abduction.Abducible
  ( Abducible(..)
  , FreshNameMapping(..)
--  , fvmFlatten
--  , fvmFromAbducibles
  ) where

import           Control.Monad (foldM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Orhle.Imp
import           Orhle.Names
import qualified Orhle.SMT as SMT


data Abducible = Abducible
  { abdName   :: String
  , abdParams :: [Name]
  } deriving (Ord, Eq)

instance Show Abducible where
  show (Abducible name params) =
    "(" ++ name ++ ", params: " ++ (show params) ++ ")"

--------------------------------------------------------------------------------

data FreshNameMapping = FreshNameMapping
  { fvmOrigToFresh :: Map.Map Name Name
  , fvmFreshToOrig :: Map.Map Name Name
  , fvmOrigAbds    :: Set.Set Abducible
  , fvmFreshAbds   :: Set.Set Abducible
  }

fvmEmpty :: FreshNameMapping
fvmEmpty = FreshNameMapping Map.empty Map.empty Set.empty Set.empty

fvmInsert :: Abducible -> Abducible -> FreshNameMapping -> FreshNameMapping
fvmInsert abdOrig abdFresh fvm =
  FreshNameMapping origToFresh' freshToOrig' origAbds' freshAbds'
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

-- fvmReplacementTerm :: FreshNameMapping -> Abducible -> SMT SMT.Expr
-- fvmReplacementTerm fvm abd = do
--   let varToAST = \v -> mkStringSymbol v >>= mkIntName
--   abdNameASTs   <- sequence $ map varToAST $ abdParams abd
--   freshNameASTs <- sequence $ map varToAST $ freshNames
--   eqTerms      <- sequence $ map (uncurry mkEq) $ zip abdNameASTs freshNameASTs
--   mkAnd eqTerms
--     where freshNames = map (fvmOrigToFresh fvm Map.!) (abdParams abd)

-- fvmFromAbducibles :: [Abducible] -> SMT FreshNameMapping
-- fvmFromAbducibles abds = foldM insertAbd fvmEmpty abds
--   where
--     insertAbd fvm abd@(Abducible abdNameStr abdParamNames) = do
--         freshAbdParamASTs <- mkFreshIntNames abdParamNames
--         freshAbdParamNames <- mapM astToString freshAbdParamASTs
--         let freshAbd = Abducible abdNameStr freshAbdParamNames
--         return $ fvmInsert abd freshAbd fvm

-- fvmFlatten :: FreshNameMapping -> SMT.Expr -> SMT SMT.Expr
-- fvmFlatten fvm phi = foldM flattenAbd phi (fvmOrigAbds fvm)
--   where
--     flattenAbd :: SMT.Expr -> Abducible -> SMT SMT.Expr
--     flattenAbd phi' abd = do
--       abdAST      <- mkBoolName =<< mkStringSymbol (abdName abd)
--       replacement <- fvmReplacementTerm fvm abd
--       substitute phi' [abdAST] [replacement]
