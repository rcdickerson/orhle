module HoareE
  ( mkHLETrip
  , HLETrip(..)
  , hleSP
  ) where

import Imp
import Z3.Monad
import Z3Util

data HLETrip = HLETrip
  { hlePre  :: AST
  , hleProg :: Prog
  , hlePost :: AST
  } deriving (Show)

mkHLETrip :: String -> Prog -> String -> Z3 HLETrip
mkHLETrip pre prog post = do
  preAST  <- parseSMT pre
  postAST <- parseSMT post
  return $ HLETrip preAST prog postAST

hleSP :: Stmt -> AST -> Z3 AST
hleSP stmt pre = do
  case stmt of
    Skip        -> return pre
    var := aexp -> assignPost var aexp pre
    Seq []      -> return pre
    Seq (s:ss)  -> hleSP (Seq ss) =<< hleSP s pre
    If b s1 s2  -> do
      c    <- bexpToZ3 b
      notC <- mkNot c
      imp1 <- mkImplies c    =<< hleSP s1 pre
      imp2 <- mkImplies notC =<< hleSP s2 pre
      mkAnd [imp1, imp2]
    Call _ f    -> funSP f pre
