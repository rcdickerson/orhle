module Abduction
    ( abduce
    , Abduction
    , emptyIMap
    , imapInit
    , imapStrengthen
    , imapCondUnion
    , InterpMap
    , InterpResult(..)
    , ppInterpMap
    , putInterpMap
    , singletonIMap
    ) where

import Conditions
import Data.Foldable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Imp
import Simplify
import Z3.Monad
import Z3Util

type Abduction = ([Var], [AST], [AST])

type InterpMap = Map.Map Var AST

data InterpResult = IRSat InterpMap
                  | IRUnsat
                  deriving(Show)

-------------------------
-- Interpretation Maps --
------------------------

emptyIMap = Map.empty
singletonIMap var duc = Map.singleton var duc

putInterpMap :: InterpMap -> IO ()
putInterpMap imap = mapM_ putInterpLine (Map.toList imap)
  where putInterpLine = \(var, ast) -> do
          interp <- evalZ3 $ astToString =<< simplify ast
          putStrLn $ "  " ++ var ++ ": " ++ interp

ppInterpMap :: InterpMap -> Z3 [String]
ppInterpMap imap = mapM line (Map.toList imap)
  where line = \(var, ast) -> do
          interp <- astToString =<< simplify ast
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
                     initPostCond <- condToZ3.fPostCond $ f
                     -- TODO: Need to make the name unique for callsite...
                     callsiteFun <- mkFreshFuncDecl (fName f) [] =<< mkIntSort
                     return $ Map.insert var initPostCond emptyIMap

imapCondUnion :: (Cond, InterpMap) -> (Cond, InterpMap) -> Z3 InterpMap
imapCondUnion (cond1, imap1) (cond2, imap2) =  Map.traverseWithKey (condUnionWith imap1) imap2
    where
      condUnionWith imap abd interp1 = do
        impl1 <- (flip mkImplies) interp1 =<< condToZ3 cond1
        case (Map.lookup abd imap) of
          Nothing      -> return impl1
          Just interp2 -> do
            impl2 <- (flip mkImplies) interp2 =<< condToZ3 cond2
            mkAnd [impl1, impl2]

imapStrengthen :: Cond -> InterpMap -> Cond -> Z3 InterpResult
imapStrengthen pre imap post = do
  let vars = Map.keys imap
  freshVars <- mapM (\v -> mkFreshIntVar v >>= astToString >>= \f -> return (v, f)) vars
  let subFresh = \pre' (v, f) -> csubst pre' v (V f)
  preZ3  <- condToZ3 $ foldl subFresh pre freshVars
  postZ3 <- condToZ3 post
  abduce (vars, [preZ3], postZ3:(Map.elems imap))

imapConjoin :: InterpMap -> Z3 AST
imapConjoin imap = mkAnd $ map snd $ Map.toList imap


---------------
-- Abduction --
---------------

abduce :: Abduction -> Z3 InterpResult
abduce (vars, pres, posts) = do
  preConds  <- mkAnd pres
  consistencyCheck <- checkSat preConds
  if not consistencyCheck
    then return IRUnsat
    else do
      postConds <- mkAnd posts
      case vars of
        []     -> noAbduction          preConds postConds
        var:[] -> singleAbduction var  preConds postConds
        _      -> multiAbduction  vars preConds postConds

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

noAbduction :: AST -> AST -> Z3 InterpResult
noAbduction conds post = do
  imp <- mkImplies conds post
  vars <- astVars imp
  sat <- checkSat =<< performQe vars imp
  if sat
    then return $ IRSat emptyIMap
    else return IRUnsat

singleAbduction :: Var -> AST -> AST -> Z3 InterpResult
singleAbduction var conds post = do
  imp   <- mkImplies conds post
  vars  <- astVars imp
  vbar  <- filterVars vars [var]
  qeRes <- performQe vbar imp
  sat   <- checkSat qeRes
  case sat of
    False -> return IRUnsat
    True  -> do
      qeResSimpl <- simplifyWrt conds qeRes
      return $ IRSat $ Map.insert var qeResSimpl emptyIMap

multiAbduction :: [Var] -> AST -> AST -> Z3 InterpResult
multiAbduction vars conds post = do
  let combinedDuc = "_combined"
  combinedResult <- singleAbduction combinedDuc conds post
  case combinedResult of
    IRUnsat    -> return IRUnsat
    IRSat imap -> return.IRSat =<< cartDecomp vars conds (imap Map.! combinedDuc)

cartDecomp :: [Var] -> AST -> AST -> Z3 InterpMap
cartDecomp vars conds combinedResult = do
  initMap <- initSolution vars conds combinedResult
  foldlM replaceWithDecomp initMap vars
  where
    replaceWithDecomp :: InterpMap -> Var -> Z3 InterpMap
    replaceWithDecomp imap var = do
      dec <- decompose var imap
      return $ Map.union dec imap
    decompose :: Var -> InterpMap -> Z3 InterpMap
    decompose var imap = do
      post <- imapConjoin $ Map.restrictKeys imap $ Set.singleton var
      ires <- abduce ([var], [conds], [post])
      case ires of
        IRUnsat     -> error $ "Unable to decompose " ++ (show combinedResult)
        IRSat imap' -> return imap'

initSolution :: [Var] -> AST -> AST -> Z3 InterpMap
initSolution vars conds post = do
  model <- modelOrError =<< mkAnd [conds, post]
  foldlM (getInterpOrError model) (Map.empty) vars
  where
    getInterpOrError :: Model -> InterpMap -> Var -> Z3 InterpMap
    getInterpOrError model imap var = do
      varSymb <- mkStringSymbol $ var
      varDecl <- mkFuncDecl varSymb [] =<< mkIntSort
      interp  <- getConstInterp model varDecl
      case interp of
        Nothing -> error $ "Unable to model value for " ++ var
        Just v  -> do
          eqv <- mkEq v =<< aexpToZ3 (V $ var)
          return $ Map.insert var eqv imap


performQe :: [Symbol] -> AST -> Z3 AST
performQe vars formula = do
  push
  intVars <- mapM mkIntVar vars
  appVars <- mapM toApp intVars
  qf <- mkForallConst [] appVars formula
  goal <- mkGoal False False False
  goalAssert goal qf
  qe <- mkTactic "qe"
  qeResult <- applyTactic qe goal
  subgoals <- getApplyResultSubgoals qeResult
  formulas <- mapM getGoalFormulas subgoals
  pop 1
  mkAnd $ concat formulas

modelOrError :: AST -> Z3 Model
modelOrError ast = do
  push
  assert ast
  res <- getModel
  pop 1
  case res of
    (Sat, Just model) -> return model
    _ -> do
      astStr <- astToString ast
      error $ "Unable to model " ++ astStr
