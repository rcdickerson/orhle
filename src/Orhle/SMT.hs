module Orhle.SMT
  ( SatResult(..)
  , ValidResult(..)
  , checkSat
  , checkValid
  , cnf
  , simplify
  , splitClauses
  ) where

import qualified Data.Set as Set
import qualified Orhle.Assertion as A
import           Orhle.Name ( Name(..), TypedName(..) )
import qualified Orhle.Name as Name
import           Orhle.SMTString ( showSMT )
import qualified SimpleSMT as SSMT
import qualified SMTLib2 as S
import           SMTLib2.Core ( tBool )
import           SMTLib2.Int  ( tInt )
import qualified Text.PrettyPrint as PP

data SatResult = Sat String | Unsat | SatUnknown
data ValidResult = Valid | Invalid String | ValidUnknown

checkValid :: Bool -> A.Assertion -> IO ValidResult
checkValid logOutput assertion = do
  satResult <- checkSat logOutput (A.Not assertion)
  return $ case satResult of
    Sat model  -> Invalid model
    Unsat      -> Valid
    SatUnknown -> ValidUnknown

checkSat :: Bool -> A.Assertion -> IO SatResult
checkSat logOutput assertion = do
    solver <- if logOutput
              then (SSMT.newSolver "z3" ["-in"]) . Just =<< SSMT.newLogger 0
              else SSMT.newSolver "z3" ["-in"] Nothing
    declareFVs solver assertion
    SSMT.assert solver $ toSSMT assertion
    result <- SSMT.check solver
    case result of
      SSMT.Sat -> do
        model <- SSMT.command solver $ SSMT.List [SSMT.Atom "get-model"]
        let sat = Sat $ SSMT.showsSExpr model ""
        SSMT.stop solver
        return sat
      SSMT.Unsat   -> SSMT.stop solver >> return Unsat
      SSMT.Unknown -> SSMT.stop solver >> return SatUnknown

simplify :: A.Assertion -> IO (Either String A.Assertion)
simplify assertion = let
  fvs         = Set.toList $ A.freeVars assertion
  declareVars = map toDeclareConst fvs
  (SSMT.Atom assertionSSMT) = toSSMT assertion
  ssmt = SSMT.Atom $ "(simplify " ++ assertionSSMT ++ ")"
  in do
    logger <- SSMT.newLogger 0
    solver <- SSMT.newSolver "z3" ["-in"] Nothing -- $ Just logger
    mapM_ (SSMT.ackCommand solver) declareVars
    result <- parseResult "simplify" A.parseAssertion =<< SSMT.command solver ssmt
    SSMT.stop solver
    return result

cnf :: A.Assertion -> IO (Either String A.Assertion)
cnf assertion = do
  logger <- SSMT.newLogger 0
  solver <- SSMT.newSolver "z3" ["-in"] Nothing -- $ Just logger
  declareFVs solver assertion
  SSMT.ackCommand solver $ SSMT.Atom $ "(assert " ++ showSMT assertion ++ ")"
  result  <- SSMT.command solver $ SSMT.Atom "(apply tseitin-cnf)"
  SSMT.stop solver
  pResult <- parseResult "cnf" A.parseGoals result
  case pResult of
    Right goals -> return $ Right $ A.And $ concat goals
    Left err    -> return $ Left err

splitClauses :: A.Assertion -> IO (Either String [A.Assertion])
splitClauses assertion = do
  logger <- SSMT.newLogger 0
  solver <- SSMT.newSolver "z3" ["-in"] Nothing -- $ Just logger
  declareFVs solver assertion
  SSMT.ackCommand solver $ SSMT.Atom $ "(assert " ++ showSMT assertion ++ ")"
  SSMT.command solver $ SSMT.Atom "(apply tseitin-cnf)"
  result  <- SSMT.command solver $ SSMT.Atom "(apply (then simplify (repeat (or-else split-clause skip))))"
  SSMT.stop solver
  pResult <- parseResult "splitClauses" A.parseGoals result
  case pResult of
    Right goals -> return $ Right $ map A.And goals
    Left err    -> return $ Left err

declareFVs :: SSMT.Solver -> A.Assertion -> IO ()
declareFVs solver assertion = let
  fvs         = Set.toList $ A.freeVars assertion
  declareVars = map toDeclareConst fvs
  in mapM_ (SSMT.ackCommand solver) declareVars

parseResult :: String -> (String -> Either A.ParseError a) -> SSMT.SExpr -> IO (Either String a)
parseResult description parser result =
  let resultStr = SSMT.showsSExpr result ""
  in case parser resultStr of
    Left err -> return . Left $ unlines [
      "Unable to " ++ description ++ ", parse error: ",
      "  " ++ show err,
      "  on SMT result:" ++ resultStr]
    Right a  -> return . Right $ a

-- We want to encode assertions using smt-lib types, but simple-smt declares its
-- own (simple, but weak) s-expression type. So, right before we interact with a
-- simple-smt solver, we shunt smt-lib expressions into simple-smt s-expressions
-- by relying on smt-lib's s-expression pretty printer.
--
-- This solution is not very elegant: Orhle.Assertion -> SMT-Lib -> Simple-SMT
-- is an overly long representation pipeline, and relying on SMT-Lib pretty
-- printing is fragile. While it is possible to go straight from Orhle.Assertion
-- -> Simple-SMT s-expressions, I am keeping the SMT-Lib middleman for now
-- because 1) SMT-Lib's stronger typing helps exclude bugs in the translation
-- from Assertion and 2) the SMT-Lib representation seems more likely to be
-- adaptable to other solver backends if we want to move away from Simple-SMT in
-- the future. ~RCD
-- toSSMT :: S.PP a => a -> SSMT.SExpr
-- toSSMT = SSMT.Atom . PP.render . S.pp

toSSMT :: A.Assertion -> SSMT.SExpr
toSSMT = SSMT.Atom . showSMT

--------------------
-- SMT Embeddings --
--------------------

-- class SMTEmbeddable a where
--   toSMT :: a -> S.Expr

-- instance SMTEmbeddable TypedName where
--   toSMT (TypedName name _) = S.app (stringToSIdent $ nameStr name) []

-- instance SMTEmbeddable A.Arith where
--   toSMT arith = case arith of
--     A.Num n     -> S.Lit $ S.LitNum n
--     A.Var ident -> toSMT ident
--     A.Add as    -> toApp "+"   as
--     A.Sub as    -> toApp "-"   as
--     A.Mul as    -> toApp "*"   as
--     A.Div a1 a2 -> toApp "/"   [a1, a2]
--     A.Mod a1 a2 -> toApp "mod" [a1, a2]
--     A.Pow a1 a2 -> toApp "^"   [a1, a2]

-- instance SMTEmbeddable A.Assertion where
--   toSMT assertion = case assertion of
--     A.ATrue        -> toApp "true"  ([]::[A.Assertion])
--     A.AFalse       -> toApp "false" ([]::[A.Assertion])
--     A.Atom ident   -> toSMT ident
--     A.Not  a       -> toApp "not" [a]
--     A.And  as      -> toApp "and" as
--     A.Or   as      -> toApp "or"  as
--     A.Imp  a1 a2   -> toApp "=>"  [a1, a2]
--     A.Eq   a1 a2   -> toApp "="   [a1, a2]
--     A.Lt   a1 a2   -> toApp "<"   [a1, a2]
--     A.Gt   a1 a2   -> toApp ">"   [a1, a2]
--     A.Lte  a1 a2   -> toApp "<="  [a1, a2]
--     A.Gte  a1 a2   -> toApp ">="  [a1, a2]
--     A.Forall ids a -> S.Quant S.Forall (map toBinder ids) (toSMT a)
--     A.Exists ids a -> S.Quant S.Exists (map toBinder ids) (toSMT a)
--     A.Hole _ _     -> error "Unable to embed assertion with hole in SMT"

-- stringToSIdent :: String -> S.Ident
-- stringToSIdent str = S.I (S.N str) []

-- toApp :: SMTEmbeddable a => String -> [a] -> S.Expr
-- toApp f as = S.app (stringToSIdent f) (map toSMT as)

-- toBinder :: TypedName -> S.Binder
-- toBinder (TypedName name sort) = case sort of
--   Name.Bool -> S.Bind (S.N $ nameStr name) tBool
--   Name.Int  -> S.Bind (S.N $ nameStr name) tInt

--toDeclareConst :: TypedName -> S.Command
--toDeclareConst (TypedName name sort) = case sort of
--  Name.Bool -> S.CmdDeclareConst (S.N $ nameStr name) tBool
--  Name.Int  -> S.CmdDeclareConst (S.N $ nameStr name) tInt

nameStr :: Name -> String
nameStr (Name name 0) = name
nameStr (Name name i) = name ++ "!" ++ show i

toDeclareConst :: TypedName -> SSMT.SExpr
toDeclareConst (TypedName name sort) = case sort of
  Name.Bool -> SSMT.Atom $ "(declare-const " ++ nameStr name ++ " Bool)"
  Name.Int  -> SSMT.Atom $ "(declare-const " ++ nameStr name ++ " Int)"
