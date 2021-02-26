{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
module Orhle.SMTMonad
  ( module Orhle.SMTMonad
  , Expr
  , Type
  )
where

import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Map                       ( Map )
import qualified Data.Map                      as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import qualified Text.PrettyPrint              as PP

import           SimpleSMT                      ( Result(..)
                                                , SExpr(..)
                                                , ackCommand
                                                , assert
                                                , check
                                                , command
                                                , newLogger
                                                , newSolver
                                                , showsSExpr
                                                )
import           SMTLib2
import           SMTLib2.Core
import           SMTLib2.Int

-- State keeps track of fresh variables
newtype SMT a = SMT (WriterT (Set Name) (State Int) a)
  deriving (Functor, Applicative, Monad, MonadWriter (Set Name), MonadState Int)

newtype Symbol = Symbol Name
  deriving (Eq, Ord)

mkStringSymbol :: String -> SMT Symbol
mkStringSymbol = return . Symbol . N

getSymbolString :: Symbol -> SMT String
getSymbolString (Symbol (N s)) = return s

mkBoolSort :: SMT Type
mkBoolSort = return tBool

mkIntSort :: SMT Type
mkIntSort = return tInt

mkRealSort :: SMT Type
mkRealSort = return "Real"

mkUninterpretedSort :: Symbol -> SMT Type
mkUninterpretedSort (Symbol s) = error "TODO: is this ever actually used?"

mkIntVar :: Symbol -> SMT Expr
mkIntVar (Symbol s) = do
  tell (Set.singleton s)
  return (app (I s []) [])

mkTrue :: SMT Expr
mkTrue = return true

mkFalse :: SMT Expr
mkFalse = return false

mkNot :: Expr -> SMT Expr
mkNot = return . SMTLib2.Core.not

mkImplies :: Expr -> Expr -> SMT Expr
mkImplies a b = return $ a ==> b

mkAnd :: [Expr] -> SMT Expr
mkAnd = return . app "and"

mkOr :: [Expr] -> SMT Expr
mkOr = return . app "or"

mkEq :: Expr -> Expr -> SMT Expr
mkEq a b = return $ app "=" [a, b]

mkLe :: Expr -> Expr -> SMT Expr
mkLe a b = return $ nLeq a b

mkLt :: Expr -> Expr -> SMT Expr
mkLt a b = return $ nLt a b

mkGe :: Expr -> Expr -> SMT Expr
mkGe a b = return $ nGeq a b

mkGt :: Expr -> Expr -> SMT Expr
mkGt a b = return $ nGt a b

mkIntNum :: Integral a => a -> SMT Expr
mkIntNum = return . num

mkInteger :: Integer -> SMT Expr
mkInteger = return . num

mkAdd :: [Expr] -> SMT Expr
mkAdd = return . app "+"

mkSub :: [Expr] -> SMT Expr
mkSub = return . app "-"

mkMul :: [Expr] -> SMT Expr
mkMul = return . app "*"

mkDiv :: Expr -> Expr -> SMT Expr
mkDiv a b = return $ nDiv a b

mkMod :: Expr -> Expr -> SMT Expr
mkMod a b = return $ nMod a b

-- non-standard, but supported by Z3
mkPower :: Expr -> Expr -> SMT Expr
mkPower a b = return $ app "^" [a, b]

mkForallConst :: [Name] -> Expr -> SMT Expr
mkForallConst binders body =
  return $ Quant Forall (map (flip Bind tInt) binders) body

mkExistsConst :: [Name] -> Expr -> SMT Expr
mkExistsConst binders body =
  return $ Quant Exists (map (flip Bind tInt) binders) body

toApp :: Expr -> SMT Name
toApp (App (I n []) _ _) = return n

stringsToApps :: [String] -> SMT [Name]
stringsToApps = mapM (toApp <=< mkIntVar <=< mkStringSymbol)

substituteByName :: Expr -> [String] -> [String] -> SMT Expr
substituteByName expr targets replacements =
  substitute expr targets =<< mapM (mkIntVar <=< mkStringSymbol) replacements

substitute :: Expr -> [String] -> [Expr] -> SMT Expr
substitute expr targets replacements =
  return $ substitute' expr (Map.fromList (zip targets replacements))

substitute' :: Expr -> Map String Expr -> Expr
substitute' expr subMap = go expr
 where
  go :: Expr -> Expr
  go e@(Lit _                ) = e
  go e@(App (I (N s) []) t []) = Map.findWithDefault e s subMap
  go (  App i            t es) = App i t (map go es)
  go (Quant q bs body) =
    let subMap' = withoutKeys (map (\(Bind (N s) _) -> s) bs)
    in  Quant q bs (substitute' body subMap')
  go (Let ds body) =
    let subMap' = withoutKeys (map (\(Defn (N s) _) -> s) ds)
    in  Let (map (\(Defn n e) -> Defn n (go e)) ds) (substitute' body subMap')
  go (Annot e as) = Annot (go e) (map (\(Attr n v) -> Attr n (go <$> v)) as)

  withoutKeys = Map.withoutKeys subMap . Set.fromList

exprFreeVars :: Expr -> [Symbol]
exprFreeVars = map Symbol . Set.toList . go
 where
  go (Lit _) = Set.empty
  go (App (I n _) _ []) = if isBoolLit n then Set.empty else Set.singleton n
  go (App (I n _) _ es) = Set.unions (map go es)
  go (Quant _ bs body) = go body `Set.difference` Set.fromList (map bindVar bs)
  go (Let ds body) = go body `Set.difference` Set.fromList (map defVar ds)
  go (Annot e _) = go e

  isBoolLit (N s) = s == "true" || s == "false"

exprToString :: Expr -> String
exprToString = PP.render . pp

simplify :: Expr -> SMT Expr
simplify = return

mkFreshIntVar :: String -> SMT Expr
mkFreshIntVar s = do
  n <- get
  modify (+ 1)
  mkIntVar =<< mkStringSymbol (s ++ show n)

mkFreshIntVars :: [String] -> SMT [Expr]
mkFreshIntVars = mapM mkFreshIntVar

prefixASTVars :: String -> Expr -> SMT Expr
prefixASTVars prefix ast =
  let vars  = map (\(Symbol (N s)) -> s) $ exprFreeVars ast
      pvars = map (prefix ++) vars
  in  substituteByName ast vars pvars

data Package = Package Expr (Set Name)

packageSmt :: SMT Expr -> Package
packageSmt (SMT m) = uncurry Package (evalState (runWriterT m) 0)

dumpExpr :: Package -> String
dumpExpr (Package e _) = exprToString e

newtype Model = Model String

checkValid :: Package -> IO (Maybe Model)
checkValid (Package expr vars) = do
  logger <- newLogger 0
  z3Proc <- newSolver "z3" ["-in"] Nothing
--  command z3Proc $ List [Atom "set-option", Atom ":produce-proofs", Atom "true"]
  forM_ vars $ \n -> ackCommand z3Proc $ pp2atom $ CmdDeclareConst n tInt
  assert z3Proc (pp2atom (SMTLib2.Core.not expr))
  res <- check z3Proc
  case res of
    Sat -> do
      model <- command z3Proc $ List [Atom "get-model"]
      return $ Just $ Model $ showsSExpr model ""
    Unknown -> return $ Just $ Model "<<solver returned unknown>>:\n"
    Unsat   -> return Nothing
 where
  pp2atom :: PP a => a -> SExpr
  pp2atom = Atom . PP.render . pp

modelToString :: Model -> String
modelToString (Model s) = s
