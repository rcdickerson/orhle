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
                                                )
import           Control.Monad.Except           ( ExceptT
                                                , MonadError
                                                , runExceptT
                                                , throwError
                                                )
import           Control.Monad.Reader           ( ReaderT
                                                , MonadReader
                                                , runReaderT
                                                )
import           Control.Monad.State            ( State
                                                , MonadState
                                                , runState
                                                , modify
                                                )

import qualified Language.Java.Syntax          as J
import qualified Imp                           as I

import           Control.Lens

--
-- Data types
--

data MethodSignature = MethodSignature
data TransBodyState = TransBodyState { _tbsStmts :: [I.Stmt]
                                     , _tbsTmpVarCounter :: Int
                                     }
  deriving (Show)

makeLenses ''TransBodyState

newtype TransBody a =
  TransBody (ExceptT String (ReaderT MethodSignature (State TransBodyState)) a)
  deriving (Functor, Applicative, Monad, MonadReader MethodSignature, MonadState TransBodyState, MonadError String)

runTransBody
  :: MethodSignature
  -> TransBodyState
  -> TransBody a
  -> (Either String a, TransBodyState)
runTransBody sig st (TransBody a) =
  flip runState st . flip runReaderT sig . runExceptT $ a

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
  let (e, state) = runTransBody MethodSignature (TransBodyState [] 0)
        $ mapM_ translateBlockStmt jStmts
  in  case e of
        Left err ->
          Left
            (  "error translating method:\n"
            ++ err
            ++ "\nlast state:\n"
            ++ show state
            )
        Right () -> Right $ I.SSeq $ state ^. tbsStmts

translateBlockStmt :: J.BlockStmt -> TransBody ()
translateBlockStmt (J.LocalVars _ _ decls) = mapM_ transDecl decls
 where
  transDecl :: J.VarDecl -> TransBody ()
  transDecl (J.VarDecl _ Nothing) = return () -- do nothing for uninitialized variables
  transDecl (J.VarDecl (J.VarId (J.Ident varName)) (Just (J.InitExp jExp))) =
    do
      exp <- translateExp jExp
      tbsStmts %= (++ [I.SAsgn varName exp])
      return ()
  transDecl (J.VarDecl _ _) = throwError "arrays are unsupported"
translateBlockStmt (J.BlockStmt s) = translateStmt s
translateBlockStmt (J.LocalClass _) =
  throwError "local classes are unsupported"


translateStmt :: J.Stmt -> TransBody ()
translateStmt (J.Return (Just jExp)) = do
  retExp <- translateExp jExp
  tbsStmts %= (++ [I.SAsgn "return" retExp])
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
  tbsStmts %= (++ [I.SCall [retVar] args methodName]) -- TODO: renaming?
  return (I.AVar retVar)
 where
  translateMethodName :: J.Name -> TransBody String
  translateMethodName (J.Name [J.Ident unqualName]) = return unqualName
  translateMethodName n = throwError ("unsupported name: " ++ show n)
translateExp e = throwError ("unsupported expression: " ++ show e)

--
-- Utilities
--

freshTmpVar :: TransBody I.Var
freshTmpVar = do
  n <- use tbsTmpVarCounter
  tbsTmpVarCounter += 1
  return ("$tmp" ++ show n)

ensureVar :: I.AExp -> TransBody I.Var
ensureVar (I.AVar v) = return v
ensureVar e          = do
  v <- freshTmpVar
  tbsStmts %= (++ [I.SAsgn v e])
  return v
