module Hoare
    ( hlPreAST
    , hlPostAST
     , hlSP
    , HLTrip(..)
    , hlVC
    , hlWP
    , mkHLTripFromASTs
    ) where

import Imp
import Z3.Monad
import Z3Util

data HLTrip = HLTrip
  { hlPre  :: SMTString
  , hlProg :: Prog
  , hlPost :: SMTString
  } deriving (Show)

hlPreAST :: HLTrip -> Z3 AST
hlPreAST trip = parseSMTLib2String (hlPre trip) [] [] [] []

hlPostAST :: HLTrip -> Z3 AST
hlPostAST trip = parseSMTLib2String (hlPost trip) [] [] [] []

mkHLTripFromASTs :: AST -> Prog -> AST -> Z3 HLTrip
mkHLTripFromASTs pre prog post = do
  preString  <- astToString pre
  postString <- astToString post
  return $ HLTrip preString prog postString

hlWP :: Stmt -> SMTString -> Z3 SMTString
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
      imp1 <- mkImplies c    =<< parseSMT =<< hlWP s1 post
      imp2 <- mkImplies notC =<< parseSMT =<< hlWP s2 post
      smtString =<< mkAnd [imp1, imp2]
    Call _ f    -> do
      fPreAST  <- fPreCondAST f
      fPostAST <- fPostCondAST f
      postImp  <- mkImplies fPostAST =<< parseSMT post
      smtString =<< mkAnd [fPreAST, postImp]

hlSP :: Stmt -> SMTString -> Z3 SMTString
hlSP stmt pre =
  case stmt of
    Skip        -> return pre
    var := aexp -> assignPost var aexp pre
    Seq []      -> return pre
    Seq (s:ss)  -> hlSP (Seq ss) =<< hlSP s pre
    If b s1 s2  -> do
      c    <- bexpToZ3 b
      notC <- mkNot c
      imp1 <- mkImplies c    =<< parseSMT =<< hlSP s1 pre
      imp2 <- mkImplies notC =<< parseSMT =<< hlSP s2 pre
      smtString =<< mkAnd [imp1, imp2]
    Call _ f    -> do
      preAST   <- parseSMT pre
      preImp   <- mkImplies preAST =<< fPreCondAST f
      fPostAST <- fPostCondAST f
      smtString =<< mkAnd [preImp, fPostAST]

hlVC :: HLTrip -> Z3 SMTString
hlVC (HLTrip pre prog post) = do
  preAST <- parseSMT pre
  smtString =<< mkImplies preAST =<< parseSMT =<< hlWP prog post
