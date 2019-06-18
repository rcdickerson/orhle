module Verifier1
    ( encodeImp
    , verify1
    ) where

import Abduction
import Conditions
import Imp
import RHLE
import Z3.Monad

verify1 :: RHLETrip -> Z3 InterpResult
verify1 (RHLETrip pre progA progE post) = do
  let (cA, aA) = encodeImp progA
  let (cE, aE) = encodeImp progE
  let fPosts = conjoin $ map (fPostCond.snd) (aA ++ aE)
  preConds  <- mapM condToZ3 [pre, cA, cE]
  postConds <- mapM condToZ3 [post, fPosts]
  abduce (fst.unzip $ aA ++ aE, preConds, postConds)

encodeImp :: Stmt -> (Cond, [(Var, UFunc)])
encodeImp stmt =
  case stmt of
    Skip       -> (CTrue, [])
    Seq []     -> encodeImp Skip
    Seq (s:ss) -> (CAnd c1 c2, a1 ++ a2)
                  where (c1, a1) = encodeImp(s)
                        (c2, a2) = encodeImp(Seq ss)
    lhs := rhs -> (CEq (V lhs) rhs, [])
    If b s1 s2 -> (CAnd (CImp c c1) (CImp (CNot c) c2), a1 ++ a2)
                  where (c1, a1) = encodeImp(s1)
                        (c2, a2) = encodeImp(s2)
                        c = bexpToCond b
    Call var f -> (CTrue, [(var, f)])
