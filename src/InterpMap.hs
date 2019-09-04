module InterpMap
    ( InterpMap
    , emptyIMap
    , imapInit
    , imapCondUnion
    , ppInterpMap
    , putInterpMap
    , singletonIMap
    ) where

import qualified Data.Map as Map
import Imp
import Z3.Monad

type InterpMap = Map.Map Var AST

emptyIMap :: InterpMap
emptyIMap = Map.empty

singletonIMap :: Var -> AST -> InterpMap
singletonIMap var duc = Map.singleton var duc

putInterpMap :: InterpMap -> IO ()
putInterpMap imap = mapM_ putInterpLine (Map.toList imap)
  where putInterpLine = \(var, smt) -> do
          interp <- evalZ3 $ astToString =<< simplify smt
          putStrLn $ "  " ++ var ++ ": " ++ interp

ppInterpMap :: InterpMap -> Z3 [String]
ppInterpMap imap = mapM line (Map.toList imap)
  where line = \(var, smt) -> do
          interp <- astToString =<< simplify smt
          return $ var ++ ": " ++ interp

imapInit :: Prog -> Z3 InterpMap
imapInit prog =
  case prog of
    Skip          -> return $ emptyIMap
    Seq []        -> imapInit Skip
    Seq (s:ss)    -> do
                     first <- imapInit s
                     rest  <- imapInit $ Seq ss
                     return $ Map.union first rest
    (:=) _ _      -> return $ emptyIMap
    If _ s1 s2    -> do
                     first  <- imapInit s1
                     second <- imapInit s2
                     return $ Map.union first second
    Call var f    -> do
                     -- TODO: Need to make the name unique per callsite?
                     callsiteFun <- mkFreshFuncDecl (fName f) [] =<< mkIntSort
                     fPost <- fPostCond f
                     return $ Map.insert var fPost emptyIMap

imapCondUnion :: (AST, InterpMap) -> (AST, InterpMap) -> Z3 InterpMap
imapCondUnion (cond1, imap1) (cond2, imap2) =
  Map.traverseWithKey (condUnionWith imap1) imap2
  where
    condUnionWith imap abd interp1 = do
      impl1 <- mkImplies cond1 interp1
      case (Map.lookup abd imap) of
        Nothing      -> return impl1
        Just interp2 -> do
          impl2      <- mkImplies cond2 interp2
          mkAnd [impl1, impl2]
