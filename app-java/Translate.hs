{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- References to "JLS" refer to The Java Language Specification, Third Edition (for Java SE 6)

module Translate
  ( translate
  )
where

import           Prelude                 hiding ( exp )

import           Data.Maybe                     ( fromMaybe )
import           Data.Sequence                  ( Seq(..)
                                                , fromList
                                                )
import           Control.Monad                  ( mapM_
                                                , (<=<)
                                                , void
                                                , liftM2
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
                                                , gets
                                                , modify
                                                )

import qualified Language.Java.Syntax          as J
import qualified Imp                           as I

--
-- Data types
--

type ITransStmt = I.AbsStmt String

data MethodSignature = MethodSignature
data TransBodyState = TransBodyState { tbsTmpVarCounter :: Int }
  deriving (Show)


newtype TransBody a =
  TransBody (ExceptT String (RWS MethodSignature [ITransStmt] TransBodyState) a)
  deriving (Functor, Applicative, Monad, MonadReader MethodSignature, MonadWriter [ITransStmt], MonadState TransBodyState, MonadError String)

runTransBody
  :: MethodSignature
  -> TransBodyState
  -> TransBody a
  -> (Either String a, TransBodyState, [ITransStmt])
runTransBody sig st (TransBody a) = runRWS (runExceptT a) sig st

--
-- Translation
--

translate :: J.CompilationUnit -> Either String ITransStmt
translate = translateMethodBody <=< extractSingleMethod

-- TODO: return more info
extractSingleMethod :: J.CompilationUnit -> Either String J.Block
extractSingleMethod (J.CompilationUnit _maybePackageDecl _importList [J.ClassTypeDecl (J.ClassDecl _ _className _ _ _ (J.ClassBody [J.MemberDecl (J.MethodDecl _ _ _retTy _methodIdent [] _ Nothing (J.MethodBody (Just methodBodyBlock)))]))])
  = Right methodBodyBlock
extractSingleMethod _ = Left "bad Java compilation unit"

translateMethodBody :: J.Block -> Either String ITransStmt
translateMethodBody (J.Block jStmts_l) =
  let (jStmts, lastRetJExp) = case fromList jStmts_l of
        s :|> (J.BlockStmt (J.Return jRetExp)) -> (s, jRetExp)
        s -> (s, Nothing)
      (eitherRetExp, state, stmts) =
          runTransBody MethodSignature (TransBodyState 0)
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
          Just retExp -> stmts ++ [I.SAsgn "return" retExp]
          Nothing     -> stmts

translateBlockStmt :: J.BlockStmt -> TransBody ()
translateBlockStmt (J.LocalVars _ _ decls) = mapM_ transDecl decls
 where
  transDecl :: J.VarDecl -> TransBody ()
  transDecl (J.VarDecl _ Nothing) = return () -- do nothing for uninitialized variables
  transDecl (J.VarDecl (J.VarId (J.Ident varName)) (Just (J.InitExp jExp))) =
    do
      exp <- translateExp jExp
      tell [I.SAsgn varName exp] -- TODO: shadowing?
  transDecl (J.VarDecl _ _) = throwError "arrays are unsupported"
translateBlockStmt (J.BlockStmt s) = translateStmt s
translateBlockStmt (J.LocalClass _) =
  throwError "local classes are unsupported"


translateStmt :: J.Stmt -> TransBody ()
translateStmt (J.IfThenElse jCond jThen jElse) = do
  cond        <- translateBExp jCond
  ((), iThen) <- inBlock (translateStmt jThen)
  ((), iElse) <- inBlock (translateStmt jElse)
  tell [I.SIf cond (I.SSeq iThen) (I.SSeq iElse)]
translateStmt (J.StmtBlock (J.Block jStmts)) = mapM_ translateBlockStmt jStmts
translateStmt (J.ExpStmt jExp) = void (translateExp jExp)
translateStmt (J.While jCond (J.StmtBlock (J.Block jStmts))) = do
  cond           <- translateBExp jCond
  (inv, jStmts') <- maybe (throwError "no invariant found in while loop")
                          return
                          (extractLoopAnnotation "loopInvariant" jStmts)
  let (var, jStmts'') = fromMaybe
        ("true", jStmts')
        (extractLoopAnnotation "loopVariant" jStmts')
  ((), body) <- inBlock (mapM_ translateBlockStmt jStmts'')
  tell [I.SWhile cond (I.SSeq body) (inv, var, False)]
translateStmt s = throwError ("unsupported statement: " ++ show s)


extractLoopAnnotation
  :: String -> [J.BlockStmt] -> Maybe (String, [J.BlockStmt])
extractLoopAnnotation annotationName jLoopBody = case jLoopBody of
  J.BlockStmt (J.ExpStmt (J.MethodInv jInv)) : restJStmts -> case jInv of
    (J.MethodCall (J.Name [J.Ident call]) [jArg]) | call == annotationName ->
      case jArg of
        J.Lit (J.String smtString) -> Just (smtString, restJStmts)
        _                          -> Nothing
    _ -> Nothing
  _ -> Nothing


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

freshTmpVar :: TransBody I.Var
freshTmpVar = do
  n <- gets tbsTmpVarCounter
  modify (\s -> s { tbsTmpVarCounter = n + 1 })
  return ("$tmp" ++ show n)

ensureVar :: I.AExp -> TransBody I.Var
ensureVar (I.AVar v) = return v
ensureVar e          = do
  v <- freshTmpVar
  tell [I.SAsgn v e]
  return v

inBlock :: TransBody a -> TransBody (a, [ITransStmt])
inBlock = censor (const []) . listen
