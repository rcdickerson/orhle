module Orhle.Abduction.InterpMap
    ( InterpMap
    , emptyIMap
--    , imapCondUnion
--    , ppInterpMap
--    , putInterpMap
    , singletonIMap
    ) where

import qualified Data.Map as Map
import           Orhle.Abduction.Abducible
import           Orhle.SMT  ( SMT )
import qualified Orhle.SMT as SMT

type InterpMap = Map.Map Abducible SMT.Expr

emptyIMap :: InterpMap
emptyIMap = Map.empty

singletonIMap :: Abducible -> SMT.Expr -> InterpMap
singletonIMap var duc = Map.singleton var duc

-- putInterpMap :: InterpMap -> IO ()
-- putInterpMap imap = mapM_ putInterpLine (Map.toList imap)
--   where putInterpLine = \(abd, smt) -> do
--           interp <- evalZ3 $ astToString =<< simplify smt
--           putStrLn $ "  " ++ (abdName abd) ++ ": " ++ interp

-- ppInterpMap :: InterpMap -> SMT [String]
-- ppInterpMap imap = mapM line (Map.toList imap)
--   where line = \(abd, smt) -> do
--           interp <- astToString =<< simplify smt
--           return $ (abdName abd) ++ ": " ++ interp

-- imapCondUnion :: (SMT.Expr, InterpMap) -> (SMT.Expr, InterpMap) -> SMT InterpMap
-- imapCondUnion (cond1, imap1) (cond2, imap2) =
--   Map.traverseWithKey (condUnionWith imap1) imap2
--   where
--     condUnionWith imap abd interp1 = do
--       impl1 <- mkImplies cond1 interp1
--       case (Map.lookup abd imap) of
--         Nothing      -> return impl1
--         Just interp2 -> do
--           impl2      <- mkImplies cond2 interp2
--           mkAnd [impl1, impl2]
