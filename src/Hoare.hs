module Hoare
    ( hlSP
    , HLTrip(..)
    , hlVC
    , hlWP
    , mkHLTrip
    ) where

import Imp
import Z3.Monad
import Z3Util

data HLTrip = HLTrip
  { hlPre  :: AST
  , hlProg :: Prog
  , hlPost :: AST
  } deriving (Show)

mkHLTrip :: String -> Prog -> String -> Z3 HLTrip
mkHLTrip pre prog post = do
  preAST  <- parseSMT pre
  postAST <- parseSMT post
  return $ HLTrip preAST prog postAST

hlWP :: Stmt -> AST -> Z3 AST
hlWP stmt post =
  case stmt of
    Skip        -> return post
    var := aexp -> subAexp post (V var) aexp
    Seq []      -> return post
    Seq (s:ss)  -> do
      wpRest <- hlWP (Seq ss) post
      hlWP s wpRest
    If b s1 s2  -> do
      c    <- bexpToZ3 b
      notC <- mkNot c
      imp1 <- mkImplies c    =<< hlWP s1 post
      imp2 <- mkImplies notC =<< hlWP s2 post
      mkAnd [imp1, imp2]
    Call _ f    -> do
      fPre    <- fPreCond f
      fPost   <- fPostCond f
      postImp <- mkImplies fPost post
      mkAnd [fPre, postImp]

hlSP :: Stmt -> AST -> Z3 AST
hlSP stmt pre =
  case stmt of
    Skip        -> return pre
    var := aexp -> assignPost var aexp pre
    Seq []      -> return pre
    Seq (s:ss)  -> hlSP (Seq ss) =<< hlSP s pre
    If b s1 s2  -> do
      c    <- bexpToZ3 b
      notC <- mkNot c
      imp1 <- mkImplies c    =<< hlSP s1 pre
      imp2 <- mkImplies notC =<< hlSP s2 pre
      mkAnd [imp1, imp2]
    Call _ f    -> do
      fPre    <- fPreCond f
      fPost   <- fPostCond f
      preImp   <- mkImplies pre fPre
      mkAnd [preImp, fPost]

hlVC :: HLTrip -> Z3 AST
hlVC (HLTrip pre prog post) = do
  mkImplies pre =<< hlWP prog post
