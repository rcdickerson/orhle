module Abduction
    ( abduce
    , Abduction
    , emptyIMap
    , imapInit
    , imapStrengthen
    , imapCondUnion
    , InterpMap
    , InterpResult
    , ppInterpMap
    , putInterpMap
    , singletonIMap
    ) where

import Control.Monad (foldM)
import Data.Foldable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Imp
import Simplify
import Z3.Monad
import Z3Util

type Abduction    = ([Var], [SMTString], [SMTString])
type InterpMap    = Map.Map Var SMTString
type InterpResult = Either String InterpMap

-------------------------
-- Interpretation Maps --
------------------------

emptyIMap = Map.empty
singletonIMap var duc = Map.singleton var duc

putInterpMap :: InterpMap -> IO ()
putInterpMap imap = mapM_ putInterpLine (Map.toList imap)
  where putInterpLine = \(var, smt) -> do
          interp <- evalZ3 $ astToString =<< simplify =<< parseSMT smt
          putStrLn $ "  " ++ var ++ ": " ++ interp

ppInterpMap :: InterpMap -> Z3 [String]
ppInterpMap imap = mapM line (Map.toList imap)
  where line = \(var, smt) -> do
          interp <- astToString =<< simplify =<< parseSMT smt
          return $ var ++ ": " ++ interp

imapInit :: Prog -> Z3 InterpMap
imapInit prog =
  case prog of
    Skip          -> return $ emptyIMap
    Seq []        -> imapInit Skip
    Seq (s:ss)    -> do
                     first <- imapInit s
                     rest  <- imapInit $ Seq ss
                     return $ Map.union first rest
    (:=) _ _      -> return $ emptyIMap
    If _ s1 s2    -> do
                     first  <- imapInit s1
                     second <- imapInit s2
                     return $ Map.union first second
    Call var f    -> do
                     -- TODO: Need to make the name unique per callsite?
                     callsiteFun <- mkFreshFuncDecl (fName f) [] =<< mkIntSort
                     return $ Map.insert var (fPostCond f) emptyIMap

imapCondUnion :: (SMTString, InterpMap) -> (SMTString, InterpMap) -> Z3 InterpMap
imapCondUnion (cond1, imap1) (cond2, imap2) =
  Map.traverseWithKey (condUnionWith imap1) imap2
  where
    condUnionWith imap abd interp1 = do
      cond1AST   <- parseSMT cond1
      interp1AST <- parseSMT interp1
      impl1      <- mkImplies cond1AST interp1AST
      case (Map.lookup abd imap) of
        Nothing      -> smtString impl1
        Just interp2 -> do
          cond2AST   <- parseSMT cond2
          interp2AST <- parseSMT interp2
          impl2      <- mkImplies cond2AST interp2AST
          smtString =<< mkAnd [impl1, impl2]

imapStrengthen :: SMTString -> InterpMap -> SMTString -> Z3 InterpResult
imapStrengthen pre imap post = do
  let vars      = Map.keys imap
  let freshen v = mkFreshIntVar v >>= astToString >>= \f -> return (v, f)
  let subFresh  = \pre' (v, f) -> subVar pre' v f
  freshVars     <- mapM freshen vars
  preZ3         <- foldM subFresh pre freshVars
  abduce (vars, [preZ3], post:(Map.elems imap))


---------------
-- Abduction --
---------------

abduce :: Abduction -> Z3 InterpResult
abduce (vars, pres, posts) = do
  consistencyCheck <- checkSat =<< mkAnd =<< mapM parseSMT pres
  if not consistencyCheck
    then return.Left $ "Preconditions are not consistent."
    else do
      case vars of
        []     -> noAbduction               pres posts
        var:[] -> singleAbduction var [var] pres posts
        _      -> multiAbduction  vars      pres posts

astVars :: AST -> Z3 [Symbol]
astVars ast = do
  astIsApp <- isApp ast
  case astIsApp of
    False -> return []
    True  -> do
      app      <- toApp ast
      astIsVar <- isVar ast
      numArgs  <- getAppNumArgs app
      case (numArgs, astIsVar) of
        (0, False) -> return []
        (0, True ) -> return . (:[]) =<< getDeclName =<< getAppDecl app
        _          -> appVars app
  where
    appVars :: App -> Z3 [Symbol]
    appVars app = do
      args <- getAppArgs app
      vars <- mapM astVars args
      let dedup = Set.toList . Set.fromList
      return . dedup . concat $ vars

isVar :: AST -> Z3 Bool
isVar ast = do
  name <- astToString ast
  kind <- getAstKind ast
  let nameOk = hasVarishName name
  case kind of
    Z3_APP_AST       -> return nameOk
    Z3_FUNC_DECL_AST -> return nameOk
    Z3_VAR_AST       -> return nameOk
    _                -> return False

-- This is super hacky, but I don't see another way to
-- distinguish actual variables in Z3.
hasVarishName :: String -> Bool
hasVarishName s = not.elem s $ ["true", "false"]

filterVars :: [Symbol] -> [Var] -> Z3 [Symbol]
filterVars symbols vars = do
  symbolStrs <- mapM getSymbolString symbols
  let notInVars = not.(flip elem) vars
  let filteredStrs = filter notInVars symbolStrs
  mapM mkStringSymbol filteredStrs

noAbduction :: [SMTString] -> [SMTString] -> Z3 InterpResult
noAbduction conds posts = do
  condAST <- mkAnd =<< mapM parseSMT conds
  postAST <- mkAnd =<< mapM parseSMT posts
  imp     <- mkImplies condAST postAST
  vars    <- astVars imp
  sat     <- checkSat =<< performQe vars imp
  if sat
    then return.Right $ emptyIMap
    else return.Left  $ "Preconditions do not imply postconditions."

singleAbduction :: String -> [Var] -> [SMTString] -> [SMTString]
                -> Z3 InterpResult
singleAbduction name vars conds posts = do
  condAST <- mkAnd =<< mapM parseSMT conds
  postAST <- mkAnd =<< mapM parseSMT posts
  imp     <- mkImplies condAST postAST
  impVars <- astVars imp
  vbar    <- filterVars impVars vars
  qeRes   <- performQe vbar imp
  sat     <- checkSat qeRes
  case sat of
    False -> return.Left $ "No satisfying abduction found."
    True  -> do
      qeResSimpl <- smtString =<< simplifyWrt condAST qeRes
      return.Right $ Map.insert name qeResSimpl emptyIMap

multiAbduction :: [Var] -> [SMTString] -> [SMTString] -> Z3 InterpResult
multiAbduction vars conds posts = do
  let combinedDuc = "_combined"
  combinedResult <- singleAbduction combinedDuc vars conds posts
  case combinedResult of
    Left  err  -> return.Left $ err
    Right imap -> cartDecomp vars conds (imap Map.! combinedDuc)

cartDecomp :: [Var] -> [SMTString] -> SMTString -> Z3 InterpResult
cartDecomp vars conds combinedResult = do
  initMap <- initSolution vars conds combinedResult
  foldlM (replaceWithDecomp combinedResult) initMap vars
  where
    replaceWithDecomp :: SMTString -> InterpResult -> Var -> Z3 InterpResult
    replaceWithDecomp _    (Left err)   _   = return.Left $ err
    replaceWithDecomp post (Right imap) var = do
      decResult <- (decompose post) var imap
      case decResult of
        Left  err -> return.Left  $ err
        Right dec -> return.Right $ Map.union dec imap
    decompose :: SMTString -> Var -> InterpMap -> Z3 InterpResult
    decompose post var imap = do
      let complement = Map.withoutKeys imap $ Set.singleton var
      ires <- abduce ([var], map snd $ Map.toList complement, [post])
      case ires of
        Left  err   -> return.Left $ "Unable to decompose " ++ (show combinedResult)
                       ++ ": " ++ err
        Right imap' -> return.Right $ imap'

initSolution :: [Var] -> [SMTString] -> SMTString -> Z3 InterpResult
initSolution vars conds combinedResult = do
  condAST  <- mkAnd =<< mapM parseSMT conds
  postAST  <- parseSMT combinedResult
  modelRes <- modelAST =<< mkAnd [condAST, postAST]
  case modelRes of
    Left  err   -> return.Left $ err
    Right model -> foldlM (getInterp model) (Right Map.empty) vars
  where
    getInterp :: Model -> InterpResult -> Var -> Z3 InterpResult
    getInterp _     (Left  err)  _   = return.Left $ err
    getInterp model (Right imap) var = do
      varSymb <- mkStringSymbol $ var
      varDecl <- mkFuncDecl varSymb [] =<< mkIntSort
      interp  <- getConstInterp model varDecl
      case interp of
        Nothing -> return.Left $ "Unable to model value for " ++ var
        Just v  -> do
          eqv <- smtString =<< mkEq v =<< aexpToZ3 (V $ var)
          return.Right $ Map.insert var eqv imap


performQe :: [Symbol] -> AST -> Z3 AST
performQe vars formula = do
  push
  intVars  <- mapM mkIntVar vars
  appVars  <- mapM toApp intVars
  qf       <- mkForallConst [] appVars formula
  goal     <- mkGoal False False False
  goalAssert goal qf
  qe       <- mkTactic "qe"
  qeResult <- applyTactic qe goal
  subgoals <- getApplyResultSubgoals qeResult
  formulas <- mapM getGoalFormulas subgoals
  pop 1
  mkAnd $ concat formulas

modelAST :: AST -> Z3 (Either String Model)
modelAST ast = do
  push
  assert ast
  res <- getModel
  pop 1
  case res of
    (Sat, Just model) -> return.Right $ model
    _ -> do
      astStr <- astToString ast
      return.Left $ "Unable to model " ++ astStr
