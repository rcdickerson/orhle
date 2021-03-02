-- EXPLAIN paper:
-- https://www.cs.utexas.edu/~isil/cav2013-tool.pdf

-- Simplification Algorithm:
-- https://theory.stanford.edu/~aiken/publications/papers/sas10.pdf

module Orhle.Abduction.Simplify
  ( simplifyWrt
  )
where

import Data.List
import Orhle.Assertion
import qualified Orhle.SMT as SMT

data NodeType = NTLeaf | NTAnd | NTOr

simplifyWrt :: Assertion -> Assertion -> IO Assertion
simplifyWrt wrt expr = do return expr
  -- wrt'  <- nnf wrt
  -- expr' <- nnf expr
  -- SMT.simplify =<< ddaSimplify wrt' expr'

-- ddaSimplify :: SMT.Expr -> SMT.Expr -> SMT SMT.Expr
-- ddaSimplify expr subexpr = do
--   (ntype, children) <- inspect subexpr
--   case ntype of
--     NTLeaf -> do
--       (nonconstraining, _) <- checkValid =<< mkImplies expr subexpr
--       (nonrelaxing, _)     <- checkValid =<< mkImplies expr =<< mkNot subexpr
--       case (nonconstraining, nonrelaxing) of
--         (True, _   ) -> mkTrue
--         (_   , True) -> mkFalse
--         _            -> return subexpr
--     NTAnd -> mkAnd =<< calcC' return expr children
--     NTOr  -> mkOr  =<< calcC' mkNot  expr children

-- -- TODO: need to repeat this until fixpoint
-- calcC' :: (SMT.Expr -> SMT SMT.Expr) -> SMT.Expr -> [SMT.Expr] -> SMT [SMT.Expr]
-- calcC' star expr asts = sequence $ mapCompList calcCi' asts
--   where
--     calcCi' :: SMT.Expr -> [SMT.Expr] -> SMT SMT.Expr
--     calcCi' x xs = do
--       xs' <- sequence $ map star xs
--       a'  <- mkAnd $ expr : xs'
--       ddaSimplify a' x

-- mapCompList :: (a -> [a] -> b) -> [a] -> [b]
-- mapCompList _ [] = []
-- mapCompList f lst@(_:xs) = snd $ foldl' f' (([], xs), []) lst
--   where
--     f' ((left, []), result) x = ((x:left, []), result')
--       where result' = (f x left) : result
--     f' ((left, right@(_:rs)), result) x = ((x:left, rs), result')
--       where result' = (f x $ left ++ right) : result

-- inspect :: SMT.Expr -> SMT (NodeType, [SMT.Expr])
-- inspect ast = do
--   astIsApp <- isApp ast
--   case astIsApp of
--     False -> return (NTLeaf, [])
--     True  -> do
--       app  <- toApp ast
--       args <- getAppArgs app
--       decl <- getAppDecl app
--       name <- getSymbolString =<< getDeclName decl
--       case name of
--         "and" -> return (NTAnd,  args)
--         "or"  -> return (NTOr,   args)
--         _     -> return (NTLeaf, args)

-- nnf :: SMT.Expr -> SMT SMT.Expr
-- nnf ast = do
--   push
--   nnfTactic <- mkTactic "nnf"
--   goal      <- mkGoal False False False
--   goalAssert goal ast
--   result    <- applyTactic nnfTactic goal
--   subgoals  <- getApplyResultSubgoals result
--   formulas  <- mapM getGoalFormulas subgoals
--   pop 1
--   mkAnd $ concat formulas
