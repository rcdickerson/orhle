module Verifier1
    ( encodeImp
    , verify1
    ) where

import Abduction
import Conditions
import Imp
import RHLE
import Z3.Monad

verify1 :: RHLETrip -> Z3 Bool
verify1 (RHLETrip pre progA progE post) = do
  let (cA, aA) = encodeImp progA
  let (cE, aE) = encodeImp progE
  let fPosts = conjoin $ map (bexpToCond.postCond.func) (aA ++ aE) -- TODO: This is not quite right
  push
  assert =<< abduce (aA ++ aE, [pre, cA, cE], CAnd post fPosts)
  result <- check
  pop 1
  case result of
    Sat -> return True
    _   -> return False

encodeImp :: Stmt -> (Cond, [Abducible])
encodeImp stmt =
  case stmt of
    Skip -> (CTrue, [])
    Seq [] -> (CTrue, [])
    Seq (s:ss) -> (CAnd c1 c2, a1 ++ a2)
                  where (c1, a1) = encodeImp(s)
                        (c2, a2) = encodeImp(Seq ss)
    lhs := rhs -> (CEq (V lhs) rhs, [])
    If b s1 s2 -> (CAnd (CImp c c1) (CImp (CNot c) c2), a1 ++ a2)
                  where (c1, a1) = encodeImp(s1)
                        (c2, a2) = encodeImp(s2)
                        c = bexpToCond b
    Call func  -> (CTrue, [Abducible func])
