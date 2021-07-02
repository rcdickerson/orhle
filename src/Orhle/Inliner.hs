--
-- Inlines all implemented function bodies into a given block of code. Fails if
-- the program contains recursion.
--

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.Inliner
  ( Inlineable(..)
  , runInline
  ) where

import           Ceili.Language.Compose( (:+:)(..) )
import           Ceili.Language.FunImp
import qualified Ceili.Name as Name
import           Control.Monad.Except
import           Control.Monad.Trans.State
import           Control.Monad.Identity
import           Data.Set  ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map

data InlineContext = Ctx { ctx_funImpls :: FunImplEnv
                         , ctx_callPath :: Set CallId
                         , ctx_freshIds :: Name.NextFreshIds
                         }
type Inliner a = StateT InlineContext (ExceptT String Identity) a

runInline :: FunImplEnv -> FunImpProgram -> Either String FunImpProgram
runInline impls prog = let
   implNames = Set.unions $ map Name.namesIn $ Map.elems impls
   progNames = Name.namesIn prog
   allNames  = Set.union progNames implNames
   freshIds  = Name.buildFreshIds allNames
   ctx       = Ctx impls Set.empty freshIds
   in runIdentity $ runExceptT $ evalStateT (inline prog) ctx

class Inlineable a where
  inline :: a -> Inliner FunImpProgram

instance (Inlineable (f e), Inlineable (g e)) => Inlineable ((f :+: g) e) where
  inline (Inl f) = inline f
  inline (Inr g) = inline g

instance Inlineable (ImpSkip e) where
  inline _ = return $ impSkip

instance Inlineable (ImpAsgn e) where
  inline (ImpAsgn l r) = return $ impAsgn l r

instance Inlineable e => Inlineable (ImpSeq e) where
  inline (ImpSeq stmts) = do
    return . impSeq =<< mapM inline stmts

instance Inlineable e => Inlineable (ImpIf e) where
  inline (ImpIf c pt pe) = do
    pti <- inline pt
    pei <- inline pe
    return $ impIf c pti pei

instance Inlineable e => Inlineable (ImpWhile e) where
  inline (ImpWhile c body meta) = do
    bodyi <- inline body
    return $ impWhileWithMeta c bodyi meta

instance Inlineable (ImpCall e) where
  inline (ImpCall cid args assignees) = inlineCall cid args assignees

instance Inlineable FunImpProgram where
  inline (In p) = inline p

inlineCall :: CallId -> [AExp] -> [Name] -> Inliner FunImpProgram
inlineCall cid args assignees = do
  failIfInPath cid
  mImpl <- lookupImpl cid
  case mImpl of
    Nothing -> return $ impCall cid args assignees
    Just impl -> do
      (FunImpl params body rets) <- freshImpl impl
      addToPath cid
      inlineBody <- inline body
      removeFromPath cid
      asgnArgs <- zipAsgn cid params args
      asgnRets <- zipAsgn cid assignees (map AVar rets)
      return $ impSeq $ asgnArgs ++ [inlineBody] ++ asgnRets

zipAsgn :: CallId -> [Name] -> [AExp] -> Inliner [FunImpProgram]
zipAsgn cid lhs rhs = do
  if (length lhs /= length rhs)
    then throwError $ "Call to function " ++ (show cid)
         ++ " with wrong number of arguments."
    else return $ map (\(l, r) -> impAsgn l r) $ zip lhs rhs

freshImpl :: FunImpl -> Inliner FunImpl
freshImpl impl = do
  Ctx implEnv path freshIds <- get
  let (freshIds', impl') = Name.runFreshen freshIds impl
  put $ Ctx implEnv path freshIds'
  return impl'

lookupImpl :: Name.Handle -> Inliner (Maybe FunImpl)
lookupImpl handle = do
  impls <- liftM ctx_funImpls get
  return $ Map.lookup handle impls

failIfInPath :: Name.Handle -> Inliner ()
failIfInPath handle = do
  path <- liftM ctx_callPath get
  if Set.member handle path
    then throwError $ "Cannot inline recursive call to " ++ handle
    else return ()

addToPath :: Name.Handle -> Inliner ()
addToPath name = do
  (Ctx impls path ids) <- get
  put $ Ctx impls (Set.insert name path) ids

removeFromPath :: Name.Handle -> Inliner ()
removeFromPath name = do
  (Ctx impls path ids) <- get
  put $ Ctx impls (Set.delete name path) ids
