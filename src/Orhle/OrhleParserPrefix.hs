-- The ORHLE parser requires some particular name prefix
-- behaviors, which this module provides.

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.OrhleParserPrefix
  ( prefixExecId
  ) where

import Ceili.Assertion
import Ceili.Language.Compose ( (:+:)(..) )
import Ceili.Language.FunImp
import qualified Ceili.Name as Name
import Data.Map ( Map )
import qualified Data.Map as Map
import Orhle.SpecImp

-- Add an execution ID prefix to all names that should have one.
class ExecIdPrefixer a where
  prefixExecId :: String -> a -> a

instance ExecIdPrefixer a => ExecIdPrefixer [a] where
  prefixExecId eid = map (prefixExecId eid)
instance (ExecIdPrefixer v) => ExecIdPrefixer (Map String v) where
  prefixExecId eid m = Map.map (prefixExecId eid) $
                       Map.mapKeysMonotonic (eid ++) m

instance ExecIdPrefixer Name where
  prefixExecId eid name = Name.prefix eid name
instance ExecIdPrefixer (AExp t) where
  prefixExecId eid aexp = Name.prefix eid aexp
instance ExecIdPrefixer (BExp t) where
  prefixExecId eid bexp = Name.prefix eid bexp
instance ExecIdPrefixer (Assertion t) where
  prefixExecId eid assertion = Name.prefix eid assertion


instance ExecIdPrefixer (ImpSkip t e) where
  prefixExecId _ = id
instance ExecIdPrefixer e => ExecIdPrefixer (ImpAsgn t e) where
  prefixExecId eid (ImpAsgn lhs rhs) = ImpAsgn (prefixExecId eid lhs) (prefixExecId eid rhs)
instance ExecIdPrefixer e => ExecIdPrefixer (ImpSeq t e) where
  prefixExecId eid (ImpSeq stmts) = ImpSeq $ map (prefixExecId eid) stmts
instance ExecIdPrefixer e => ExecIdPrefixer (ImpIf t e) where
  prefixExecId eid (ImpIf c t e) = ImpIf (prefixExecId eid c) (prefixExecId eid t) (prefixExecId eid e)
instance ExecIdPrefixer e => ExecIdPrefixer (ImpWhile t e) where
  prefixExecId eid (ImpWhile cond body meta) =
    -- While-loop metadata annotations are already addressed by their execution ID.
    ImpWhile (prefixExecId eid cond) (prefixExecId eid body) meta
instance ExecIdPrefixer (SpecCall t e) where
  prefixExecId eid (SpecCall cid params asgns) =
    SpecCall (eid ++ cid) (prefixExecId eid params) (prefixExecId eid asgns)

instance ExecIdPrefixer e => ExecIdPrefixer (FunImpl e) where
  prefixExecId eid (FunImpl params body returns) = FunImpl (prefixExecId eid params)
                                                           (prefixExecId eid body)
                                                           (prefixExecId eid returns)
instance ExecIdPrefixer (Specification t) where
  prefixExecId eid (Specification params rets cvars pre post) =
    Specification (prefixExecId eid params)
                  (prefixExecId eid rets)
                  (prefixExecId eid cvars)
                  (prefixExecId eid pre)
                  (prefixExecId eid post)

instance (ExecIdPrefixer (f e), ExecIdPrefixer (g e)) => ExecIdPrefixer ((f :+: g) e) where
  prefixExecId eid (Inl f) = Inl $ prefixExecId eid f
  prefixExecId eid (Inr g) = Inr $ prefixExecId eid g
instance ExecIdPrefixer (SpecImpProgram t) where
  prefixExecId eid (In f) = In $ prefixExecId eid f
