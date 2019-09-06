module Verifier1
    ( encodeImp
    , verify1
    ) where

import Abduction
import Control.Monad.Writer
import Imp
import InterpMap
import RHLE
import Verifier
import VTrace
import Z3.Monad

verify1 :: RHLETrip -> Z3 (VResult, [VTrace])
verify1 trip = do
  runWriterT $ verify1' trip

verify1' :: RHLETrip -> VTracedResult
verify1' (RHLETrip pre progA progE post) = do
  (cA, aA)  <- lift $ encodeImp progA
  (cE, aE)  <- lift $ encodeImp progE
  fPosts    <- lift $ mapM (fPostCond.snd) (aA ++ aE)
  result    <- lift $ abduce (fst.unzip $ aA ++ aE, [pre, cA, cE], post:fPosts)
  preStr    <- lift $ astToString =<< mkAnd [pre, cA, cE]
  postStr   <- lift $ astToString =<< mkAnd (post:fPosts)
  case result of
    Left reason -> do
      logAbductionFailure preStr postStr
      return.Left $ reason
    Right imap  -> do
      interpLines <- lift $ ppInterpMap imap
      logAbductionSuccess interpLines preStr postStr
      return.Right $ imap

encodeImp :: Stmt -> Z3 (AST, [(Var, UFunc)])
encodeImp stmt =
  case stmt of
    Skip -> do
      t <- mkTrue
      return $ (t, [])
    Seq []     -> encodeImp Skip
    Seq (s:ss) -> do
      (c1, a1) <- encodeImp s
      (c2, a2) <- encodeImp (Seq ss)
      conj     <- mkAnd [c1, c2]
      return (conj, a1 ++ a2)
    lhs := rhs -> do
      lhsAST <- aexpToZ3 (V lhs)
      rhsAST <- aexpToZ3 rhs
      eq <- mkEq lhsAST rhsAST
      return (eq, [])
    If b s1 s2 -> do
      c        <- bexpToZ3 b
      notC     <- mkNot c
      (c1, a1) <- encodeImp s1
      (c2, a2) <- encodeImp s2
      imp1     <- mkImplies c c1
      imp2     <- mkImplies notC c2
      conj     <- mkAnd [imp1, imp2]
      return (conj, a1 ++ a2)
    Call var f -> do
      t <- mkTrue
      return (t, [(var, f)])
