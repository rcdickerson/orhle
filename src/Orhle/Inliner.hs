--
-- Inlines all implemented function bodies into a given block of code. Fails if
-- the program contains recursion.
--
module Orhle.Inliner
  ( inline
  ) where

import           Control.Monad.Except
import           Control.Monad.Trans.State
import           Control.Monad.Identity
import           Data.Set  ( Set )
import qualified Data.Set as Set
import           Data.Map ( (!) )
import qualified Data.Map as Map
import           Orhle.Imp
import           Orhle.Names
import qualified Orhle.Names as Names

data InlineContext = Ctx { ctx_funImpls :: FunImplEnv
                         , ctx_callPath :: Set CallId
                         , ctx_freshIds :: Names.NextFreshIds
                         }
type Inliner a = StateT InlineContext (ExceptT String Identity) a

inline :: FunImplEnv -> Program -> Either String Program
inline impls prog = let
  implNames = Set.unions $ map namesIn $ Map.elems impls
  progNames = namesIn prog
  allNames  = Set.union progNames implNames
  freshIds  = Names.buildNextFreshIds allNames
  ctx       = Ctx impls Set.empty freshIds
  in runIdentity $ runExceptT $ evalStateT (doInline prog) ctx

doInline :: Program -> Inliner Program
doInline program = do
  case program of
    SSkip       -> return program
    SAsgn _ _   -> return program
    SSeq progs  -> return . SSeq =<< mapM doInline progs
    SIf c pt pe -> do pti <- doInline pt
                      pei <- doInline pe
                      return $ SIf c pti pei
    SWhile c body iv
                -> do bodyi <- doInline body
                      return $ SWhile c bodyi iv
    SCall cid args assignees
                -> inlineCall cid args assignees

inlineCall :: CallId -> [Name] -> [Name] -> Inliner Program
inlineCall cid args assignees = do
  failIfInPath cid
  mImpl <- lookupImpl cid
  case mImpl of
    Nothing -> return $ SCall cid args assignees
    Just impl -> do
      (FunImpl params body rets) <- freshImpl impl
      addToPath cid
      inlineBody <- doInline body
      removeFromPath cid
      asgnArgs <- zipAsgn cid params args
      asgnRets <- zipAsgn cid assignees rets
      return $ SSeq $ asgnArgs ++ [inlineBody] ++ asgnRets

zipAsgn :: CallId -> [Name] -> [Name] -> Inliner [Program]
zipAsgn cid lhs rhs = do
  if (length lhs /= length rhs)
    then throwError $ "Call to function " ++ (show cid)
         ++ " with wrong number of arguments."
    else return $ map (\(l, r) -> SAsgn l (AVar r)) $ zip lhs rhs

freshImpl :: FunImpl -> Inliner FunImpl
freshImpl impl = do
  Ctx implEnv path freshIds <- get
  let (replacements, freshIds') = Names.freshNames (namesIn impl) freshIds
  put $ Ctx implEnv path freshIds'
  return $ mapNames (replacements!) impl

lookupImpl :: Names.Handle -> Inliner (Maybe FunImpl)
lookupImpl handle = do
  impls <- liftM ctx_funImpls get
  return $ Map.lookup handle impls

failIfInPath :: Names.Handle -> Inliner ()
failIfInPath handle = do
  path <- liftM ctx_callPath get
  if Set.member handle path
    then throwError $ "Cannot inline recursive call to " ++ handle
    else return ()

addToPath :: Names.Handle -> Inliner ()
addToPath name = do
  (Ctx impls path ids) <- get
  put $ Ctx impls (Set.insert name path) ids

removeFromPath :: Names.Handle -> Inliner ()
removeFromPath name = do
  (Ctx impls path ids) <- get
  put $ Ctx impls (Set.delete name path) ids
