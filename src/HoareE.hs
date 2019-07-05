module HoareE
  ( mkHLETripFromASTs
  , hlePreAST
  , hlePostAST
  , HLETrip(..)
  , hleSP
  ) where

import Imp
import Z3.Monad
import Z3Util

data HLETrip = HLETrip
  { hlePre  :: SMTString
  , hleProg :: Prog
  , hlePost :: SMTString
  } deriving (Show)

hlePreAST :: HLETrip -> Z3 AST
hlePreAST = parseSMT.hlePre

hlePostAST :: HLETrip -> Z3 AST
hlePostAST = parseSMT.hlePost

mkHLETripFromASTs :: AST -> Prog -> AST -> Z3 HLETrip
mkHLETripFromASTs pre prog post = do
  preString  <- astToString pre
  postString <- astToString post
  return $ HLETrip preString prog postString

hleSP :: Stmt -> SMTString -> Z3 SMTString
hleSP stmt pre = do
  case stmt of
    Skip        -> return pre
    var := aexp -> assignPost var aexp pre
    Seq []      -> return pre
    Seq (s:ss)  -> hleSP (Seq ss) =<< hleSP s pre
    If b s1 s2  -> do
      c    <- bexpToZ3 b
      notC <- mkNot c
      imp1 <- mkImplies c    =<< parseSMT =<< hleSP s1 pre
      imp2 <- mkImplies notC =<< parseSMT =<< hleSP s2 pre
      smtString =<< mkAnd [imp1, imp2]
    Call _ f    -> funSP f pre
