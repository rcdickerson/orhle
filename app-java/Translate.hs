{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- References to "JLS" refer to The Java Language Specification, Third Edition (for Java SE 6)

module Translate
  ( translate
  , MethodContext(..)
  )
where

import           Prelude                 hiding ( exp )

import           Control.Monad                  ( liftM2
                                                , mapM_
                                                , void
                                                , (<=<)
                                                )
import           Control.Monad.Except           ( ExceptT
                                                , MonadError
                                                , runExceptT
                                                , throwError
                                                )
import           Control.Monad.RWS              ( MonadReader
                                                , MonadState
                                                , MonadWriter
                                                , RWS
                                                , asks
                                                , censor
                                                , gets
                                                , listen
                                                , modify
                                                , runRWS
                                                , tell
                                                )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )
import           Data.Sequence                  ( Seq(..)
                                                , fromList
                                                )

import qualified Orhle.Imp                     as I
import qualified Orhle.Assertion               as A
import qualified Language.Java.Syntax          as J

--
-- Data types
--

data MethodContext = MethodContext
    { mcLoopInvariants :: Map.Map String String
    , mcLoopVariants   :: Map.Map String String
    }
data TransBodyState = TransBodyState
    { tbsTmpVarCounter :: Int
    }
    deriving (Show)


newtype TransBody a =
  TransBody (ExceptT String (RWS MethodContext [I.Program] TransBodyState) a)
  deriving (Functor, Applicative, Monad, MonadReader MethodContext, MonadWriter [I.Program], MonadState TransBodyState, MonadError String)

runTransBody
  :: MethodContext
  -> TransBodyState
  -> TransBody a
  -> (Either String a, TransBodyState, [I.Program])
runTransBody sig st (TransBody a) = runRWS (runExceptT a) sig st

--
-- Translation
--

translate :: MethodContext -> J.CompilationUnit -> Either String I.Program
translate methodContext =
  translateMethodBody methodContext <=< extractSingleMethod

-- TODO: return more info
extractSingleMethod :: J.CompilationUnit -> Either String J.Block
extractSingleMethod (J.CompilationUnit _maybePackageDecl _importList [J.ClassTypeDecl (J.ClassDecl _ _className _ _ _ (J.ClassBody [J.MemberDecl (J.MethodDecl _ _ _retTy _methodIdent _args _ Nothing (J.MethodBody (Just methodBodyBlock)))]))])
  = Right methodBodyBlock
extractSingleMethod _ = Left "bad Java compilation unit"

translateMethodBody :: MethodContext -> J.Block -> Either String I.Program
translateMethodBody methodContext (J.Block jStmts_l) =
  let (jStmts, lastRetJExp) = case fromList jStmts_l of
        s :|> (J.BlockStmt (J.Return jRetExp)) -> (s, jRetExp)
        s -> (s, Nothing)
      (eitherRetExp, state, stmts) =
          runTransBody methodContext (TransBodyState 0)
            $  mapM_ translateBlockStmt jStmts
            >> mapM translateExp lastRetJExp
  in  case eitherRetExp of
        Left err -> Left
          (  "error translating method:\n"
          ++ err
          ++ "\nlast state:\n"
          ++ show state
          ++ "\n"
          ++ show stmts
          )
        Right maybeRetExp -> Right $ I.SSeq $ case maybeRetExp of
          Just retExp -> stmts ++ [I.SAsgn (I.Name "return" 0) retExp]
          Nothing     -> stmts

translateBlockStmt :: J.BlockStmt -> TransBody ()
-- TODO: types?
translateBlockStmt (J.LocalVars _ _ decls) = mapM_ translateVarDecl decls
translateBlockStmt (J.BlockStmt s        ) = translateStmt s
translateBlockStmt (J.LocalClass _) =
  throwError "local classes are unsupported"

translateVarDecl :: J.VarDecl -> TransBody ()
translateVarDecl (J.VarDecl (J.VarId (J.Ident varName)) (Just (J.InitExp jExp)))
  = do
    exp <- translateExp jExp
    tell [I.SAsgn (I.Name varName 0) exp] -- TODO: shadowing?
-- do nothing for uninitialized variables
translateVarDecl (J.VarDecl _ Nothing) = return ()
translateVarDecl (J.VarDecl _ _      ) = throwError "arrays are unsupported"

translateStmt :: J.Stmt -> TransBody ()
translateStmt (J.IfThenElse jCond jThen jElse) = do
  cond        <- translateBExp jCond
  ((), iThen) <- inBlock (translateStmt jThen)
  ((), iElse) <- inBlock (translateStmt jElse)
  tell [I.SIf cond (I.SSeq iThen) (I.SSeq iElse)]
translateStmt (J.IfThen jCond jThen) = do
  cond        <- translateBExp jCond
  ((), iThen) <- inBlock (translateStmt jThen)
  tell [I.SIf cond (I.SSeq iThen) I.SSkip]
translateStmt (J.StmtBlock (J.Block jStmts)) = mapM_ translateBlockStmt jStmts
translateStmt (J.ExpStmt jExp) = void (translateExp jExp)
translateStmt (J.Labeled jLabel (J.While jCond jBody)) = do
  cond        <- translateBExp jCond
  (() , body) <- inBlock (translateStmt jBody)
  (inv, var ) <- getLoopAnnotations jLabel
  tell [I.SWhile cond (I.SSeq body) (inv, var)]
translateStmt (J.Labeled jLabel (J.BasicFor jInit jCond jUpdates jBody)) = do
  case jInit of
    Just (J.ForInitExps exps      ) -> mapM_ translateExp exps
    -- TODO: types?
    Just (J.ForLocalVars _ _ decls) -> mapM_ translateVarDecl decls
    Nothing                         -> return ()
  cond       <- maybe (return I.BTrue) translateBExp jCond
  ((), body) <- inBlock $ translateStmt jBody >> mapM_ translateExp
                                                       (fromMaybe [] jUpdates)
  (inv, var) <- getLoopAnnotations jLabel
  tell [I.SWhile cond (I.SSeq body) (inv, var)]
translateStmt s = throwError ("unsupported statement: " ++ show s)

getLoopAnnotations :: J.Ident -> TransBody (A.Assertion, A.Arith)
getLoopAnnotations (J.Ident label) = do
  maybeInv <- asks (Map.lookup label . mcLoopInvariants)
  invStr   <- maybe noInvError return maybeInv
  varStr   <- asks (fromMaybe "0" . Map.lookup label . mcLoopVariants)
  let inv  = A.parseAssertion invStr
  let var  = A.parseArith varStr
  case (inv, var) of
    (Right i, Right v) -> return (i, v)
    (Left msg, _) -> error $ show msg
    (_, Left msg) -> error $ show msg
  where noInvError = throwError ("loop has no invariant: " ++ label)

-- TODO: we probably want to support more than only expressions of type int
translateExp :: J.Exp -> TransBody I.AExp
-- TODO: a simple name could refer to a local variable, parameter, or field (JLS 6.5.6.1)
translateExp (J.ExpName (J.Name [J.Ident unqualName])) =
  return (I.AVar (I.Name unqualName 0))
translateExp (J.Lit       (J.Int i                       )) = return (I.ALit i)
translateExp (J.MethodInv (J.MethodCall jMethodName jArgs)) = do
  retVar     <- freshTmpVar
  methodName <- translateMethodName jMethodName
  args       <- mapM (ensureVar <=< translateExp) jArgs
  tell [I.SCall methodName args [retVar]] -- TODO: renaming?
  return (I.AVar retVar)
 where
  translateMethodName :: J.Name -> TransBody String
  translateMethodName (J.Name [J.Ident unqualName]) = return unqualName
  translateMethodName n = throwError ("unsupported method name: " ++ show n)
translateExp (J.Assign (J.NameLhs (J.Name [J.Ident jUnqualLhsName])) J.EqualA jRhs)
  = do
    rhs <- translateExp jRhs
    tell [I.SAsgn (I.Name jUnqualLhsName 0) rhs]
    return (I.AVar (I.Name jUnqualLhsName 0))
translateExp (J.BinOp jLhs jOp jRhs) = do
  lhs <- translateExp jLhs
  rhs <- translateExp jRhs
  op  <- case jOp of
    J.Add  -> return I.AAdd
    J.Sub  -> return I.ASub
    J.Mult -> return I.AMul
    J.Div  -> return I.ADiv
    J.Rem  -> return I.AMod -- TODO: are these the same semantics?
    o      -> throwError ("unsupported arithmetic binary operation: " ++ show o)
  return (op lhs rhs)
translateExp (J.PreIncrement (J.ExpName (J.Name [J.Ident jUnqualName]))) = do
  saved <- freshTmpVar
  tell
    [ I.SAsgn (I.Name jUnqualName 0) (I.AAdd (I.AVar (I.Name jUnqualName 0)) (I.ALit 1))
    , I.SAsgn saved (I.AVar (I.Name jUnqualName 0))
    ]
  return (I.AVar saved)
translateExp (J.PostIncrement (J.ExpName (J.Name [J.Ident jUnqualName]))) = do
  saved <- freshTmpVar
  tell
    [ I.SAsgn saved (I.AVar (I.Name jUnqualName 0))
    , I.SAsgn (I.Name jUnqualName 0) (I.AAdd (I.AVar (I.Name jUnqualName 0)) (I.ALit 1))
    ]
  return (I.AVar saved)
translateExp e = throwError ("unsupported expression: " ++ show e)

-- TODO: unify with `translateExp`
translateBExp :: J.Exp -> TransBody I.BExp
translateBExp (J.BinOp jLhs jOp jRhs) = case jOp of
  J.LThan  -> liftM2 I.BLt (translateExp jLhs) (translateExp jRhs)
  J.GThan  -> liftM2 I.BGt (translateExp jLhs) (translateExp jRhs)
  J.LThanE -> liftM2 I.BLe (translateExp jLhs) (translateExp jRhs)
  J.GThanE -> liftM2 I.BGe (translateExp jLhs) (translateExp jRhs)
  J.Equal  -> liftM2 I.BEq (translateExp jLhs) (translateExp jRhs)
  J.NotEq  -> liftM2 I.BNe (translateExp jLhs) (translateExp jRhs)
  J.CAnd   -> liftM2 I.BAnd (translateBExp jLhs) (translateBExp jRhs)
  J.COr    -> liftM2 I.BOr (translateBExp jLhs) (translateBExp jRhs)
  o        -> throwError ("unsupported boolean binary operation: " ++ show o)
translateBExp e = throwError ("unsupported boolean expression: " ++ show e)

--
-- Utilities
--

freshTmpVar :: TransBody I.Name
freshTmpVar = do
  n <- gets tbsTmpVarCounter
  modify (\s -> s { tbsTmpVarCounter = n + 1 })
  return $ I.Name ("$tmp" ++ show n) 0

ensureVar :: I.AExp -> TransBody I.Name
ensureVar (I.AVar v) = return v
ensureVar e          = do
  v <- freshTmpVar
  tell [I.SAsgn v e]
  return v

inBlock :: TransBody a -> TransBody (a, [I.Program])
inBlock = censor (const []) . listen
