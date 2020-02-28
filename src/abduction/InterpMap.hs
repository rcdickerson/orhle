module InterpMap
    ( InterpMap
    , emptyIMap
    , imapCondUnion
    , ppInterpMap
    , putInterpMap
    , singletonIMap
    ) where

import Abducible
import qualified Data.Map as Map
import Z3.Monad

type InterpMap = Map.Map Abducible AST

emptyIMap :: InterpMap
emptyIMap = Map.empty

singletonIMap :: Abducible -> AST -> InterpMap
singletonIMap var duc = Map.singleton var duc

putInterpMap :: InterpMap -> IO ()
putInterpMap imap = mapM_ putInterpLine (Map.toList imap)
  where putInterpLine = \(abd, smt) -> do
          interp <- evalZ3 $ astToString =<< simplify smt
          putStrLn $ "  " ++ (abdName abd) ++ ": " ++ interp

ppInterpMap :: InterpMap -> Z3 [String]
ppInterpMap imap = mapM line (Map.toList imap)
  where line = \(abd, smt) -> do
          interp <- astToString =<< simplify smt
          return $ (abdName abd) ++ ": " ++ interp

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
