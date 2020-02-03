{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, TemplateHaskell #-}

-- References to "JLS" refer to The Java Language Specification, Third Edition (for Java SE 6)

module Translate
  ( translate
  )
where

import           Data.List                      ( intercalate )
import           Data.Functor                   ( (<&>) )
import           Data.Maybe                     ( mapMaybe )
import           Control.Monad                  ( forM
                                                , mapM_
                                                , (<=<)
                                                , void
                                                )
import           Control.Monad.Except           ( ExceptT
                                                , MonadError
                                                , runExceptT
                                                , throwError
                                                )
import           Control.Monad.RWS              ( RWS
                                                , MonadReader
                                                , MonadWriter
                                                , MonadState
                                                , runRWS
                                                , tell
                                                , listen
                                                , censor
                                                )
import           Control.Lens                   ( makeLenses )

import qualified Language.Java.Syntax          as J
import qualified Imp                           as I

import           Control.Lens.Operators

--
-- Data types
--

data MethodSignature = MethodSignature
data TransBodyState = TransBodyState { _tbsTmpVarCounter :: Int }
  deriving (Show)

makeLenses ''TransBodyState

newtype TransBody a =
  TransBody (ExceptT String (RWS MethodSignature [I.Stmt] TransBodyState) a)
  deriving (Functor, Applicative, Monad, MonadReader MethodSignature, MonadWriter [I.Stmt], MonadState TransBodyState, MonadError String)

runTransBody
  :: MethodSignature
  -> TransBodyState
  -> TransBody a
  -> (Either String a, TransBodyState, [I.Stmt])
runTransBody sig st (TransBody a) = runRWS (runExceptT a) sig st

--
-- Translation
--

translate :: J.CompilationUnit -> Either String I.Stmt
translate = translateMethodBody <=< extractSingleMethod

-- TODO: return more info
extractSingleMethod :: J.CompilationUnit -> Either String J.Block
extractSingleMethod (J.CompilationUnit maybePackageDecl importList [J.ClassTypeDecl (J.ClassDecl _ className _ _ _ (J.ClassBody [J.MemberDecl (J.MethodDecl _ _ retTy methodIdent [] _ Nothing (J.MethodBody (Just methodBodyBlock)))]))])
  = Right methodBodyBlock
extractSingleMethod _ = Left "bad Java compilation unit"

translateMethodBody :: J.Block -> Either String I.Stmt
translateMethodBody (J.Block jStmts) =
  let (e, state, stmts) =
          runTransBody MethodSignature (TransBodyState 0)
            $ mapM_ translateBlockStmt jStmts
  in  case e of
        Left err -> Left
          (  "error translating method:\n"
          ++ err
          ++ "\nlast state:\n"
          ++ show state
          ++ "\n"
          ++ show stmts
          )
        Right () -> Right (I.SSeq stmts)

translateBlockStmt :: J.BlockStmt -> TransBody ()
translateBlockStmt (J.LocalVars _ _ decls) = mapM_ transDecl decls
 where
  transDecl :: J.VarDecl -> TransBody ()
  transDecl (J.VarDecl _ Nothing) = return () -- do nothing for uninitialized variables
  transDecl (J.VarDecl (J.VarId (J.Ident varName)) (Just (J.InitExp jExp))) =
    do
      exp <- translateExp jExp
      tell [I.SAsgn varName exp]
      return ()
  transDecl (J.VarDecl _ _) = throwError "arrays are unsupported"
translateBlockStmt (J.BlockStmt s) = translateStmt s
translateBlockStmt (J.LocalClass _) =
  throwError "local classes are unsupported"


translateStmt :: J.Stmt -> TransBody ()
translateStmt (J.Return (Just jExp)) = do
  retExp <- translateExp jExp
  tell [I.SAsgn "return" retExp]
translateStmt (J.IfThenElse jCond jThen jElse) = do
  cond        <- translateBExp jCond
  ((), iThen) <- inBlock (translateStmt jThen)
  ((), iElse) <- inBlock (translateStmt jElse)
  tell [I.SIf cond (I.SSeq iThen) (I.SSeq iElse)]
translateStmt (J.StmtBlock (J.Block jStmts)) = mapM_ translateBlockStmt jStmts
translateStmt (J.ExpStmt jExp) = void (translateExp jExp)
translateStmt s = throwError ("unsupported statement: " ++ show s)

-- TODO: we probably want to support more than only expressions of type int
translateExp :: J.Exp -> TransBody I.AExp
-- TODO: a simple name could refer to a local variable, parameter, or field (JLS 6.5.6.1)
translateExp (J.ExpName (J.Name [J.Ident unqualName])) =
  return (I.AVar unqualName)
translateExp (J.Lit       (J.Int i                       )) = return (I.ALit i)
translateExp (J.MethodInv (J.MethodCall jMethodName jArgs)) = do
  retVar     <- freshTmpVar
  methodName <- translateMethodName jMethodName
  args       <- mapM (ensureVar <=< translateExp) jArgs
  tell [I.SCall [retVar] args methodName] -- TODO: renaming?
  return (I.AVar retVar)
 where
  translateMethodName :: J.Name -> TransBody String
  translateMethodName (J.Name [J.Ident unqualName]) = return unqualName
  translateMethodName n = throwError ("unsupported method name: " ++ show n)
translateExp (J.Assign (J.NameLhs (J.Name [J.Ident jUnqualLhsName])) J.EqualA jRhs)
  = do
    rhs <- translateExp jRhs
    tell [I.SAsgn jUnqualLhsName rhs]
    return (I.AVar jUnqualLhsName)
translateExp e = throwError ("unsupported expression: " ++ show e)

-- TODO: unify with `translateExp`
translateBExp :: J.Exp -> TransBody I.BExp
translateBExp (J.BinOp jLhs jOp jRhs) = do
  lhs <- translateExp jLhs
  rhs <- translateExp jRhs
  op  <- translateBOp jOp
  return (op lhs rhs)
translateBExp e = throwError ("unsupported boolean expression: " ++ show e)

translateBOp :: J.Op -> TransBody (I.AExp -> I.AExp -> I.BExp)
translateBOp J.LThan  = return I.BLt
translateBOp J.GThan  = return I.BGt
translateBOp J.LThanE = return I.BLe
translateBOp J.GThanE = return I.BGe
translateBOp J.Equal  = return I.BEq
translateBOp J.NotEq  = return I.BNe
translateBOp o =
  throwError ("unsupported boolean binary operation: " ++ show o)

--
-- Utilities
--

freshTmpVar :: TransBody I.Var
freshTmpVar = do
  n <- tbsTmpVarCounter <<+= 1
  return ("$tmp" ++ show n)

ensureVar :: I.AExp -> TransBody I.Var
ensureVar (I.AVar v) = return v
ensureVar e          = do
  v <- freshTmpVar
  tell [I.SAsgn v e]
  return v

inBlock :: TransBody a -> TransBody (a, [I.Stmt])
inBlock = censor (const []) . listen
