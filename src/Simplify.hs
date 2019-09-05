module Simplify
  ( simplifyWrt
  )
where

import Data.List
import Z3.Monad
import Z3Util

data NodeType = NTLeaf | NTAnd | NTOr

simplifyWrt :: AST -> AST -> Z3 AST
simplifyWrt wrt expr = do
  wrt'  <- nnf wrt
  expr' <- nnf expr
  simplify =<< ddaSimplify wrt' expr'

ddaSimplify :: AST -> AST -> Z3 AST
ddaSimplify expr subexpr = do
  (ntype, children) <- inspect subexpr
  case ntype of
    NTLeaf -> do
      nonconstraining <- checkValid =<< mkImplies expr subexpr
      nonrelaxing     <- checkValid =<< mkImplies expr =<< mkNot subexpr
      case (nonconstraining, nonrelaxing) of
        (True, _   ) -> mkTrue
        (_   , True) -> mkFalse
        _            -> return subexpr
    NTAnd -> mkAnd =<< calcC' return expr children
    NTOr  -> mkOr  =<< calcC' mkNot  expr children

-- TODO: need to repeat this until fixpoint
calcC' :: (AST -> Z3 AST) -> AST -> [AST] -> Z3 [AST]
calcC' star expr asts = sequence $ mapCompList calcCi' asts
  where
    calcCi' :: AST -> [AST] -> Z3 AST
    calcCi' x xs = do
      xs' <- sequence $ map star xs
      a'  <- mkAnd $ expr : xs'
      ddaSimplify a' x

mapCompList :: (a -> [a] -> b) -> [a] -> [b]
mapCompList _ [] = []
mapCompList f lst@(_:xs) = snd $ foldl' f' (([], xs), []) lst
  where
    f' ((left, []), result) x = ((x:left, []), result')
      where result' = (f x left) : result
    f' ((left, right@(_:rs)), result) x = ((x:left, rs), result')
      where result' = (f x $ left ++ right) : result

inspect :: AST -> Z3 (NodeType, [AST])
inspect ast = do
  astIsApp <- isApp ast
  case astIsApp of
    False -> return (NTLeaf, [])
    True  -> do
      app  <- toApp ast
      args <- getAppArgs app
      decl <- getAppDecl app
      name <- getSymbolString =<< getDeclName decl
      case name of
        "and" -> return (NTAnd,  args)
        "or"  -> return (NTOr,   args)
        _     -> return (NTLeaf, args)

nnf :: AST -> Z3 AST
nnf ast = do
  push
  nnfTactic <- mkTactic "nnf"
  goal      <- mkGoal False False False
  goalAssert goal ast
  result    <- applyTactic nnfTactic goal
  subgoals  <- getApplyResultSubgoals result
  formulas  <- mapM getGoalFormulas subgoals
  pop 1
  mkAnd $ concat formulas
