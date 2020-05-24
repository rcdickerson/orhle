module Verifier
  ( Verifier
  , VerifierResult
  , rhleVerifier
  , runVerifier
  ) where

import Control.Monad.Writer
import Data.List(intercalate, sort)
import qualified Data.Set as Set
import Imp
import Spec
import Triples
import VerifierTrace
import qualified SMTMonad as S

type ErrorMsg = String
type SuccessMsg = String

type Verifier       = S.SMT (FunSpecMaps, RHLETrip) -> IO VerifierResult
type VerifierResult = (Either ErrorMsg SuccessMsg, [VerifierTrace])

data VCQuant = VCUniversal | VCExistential deriving Show

runVerifier :: Verifier
               -> FunSpecMaps
               -> String -> [Prog] -> [Prog] -> String
               -> IO String
runVerifier verifier specs pre aProgs eProgs post = do
  (_, result) <- runWriterT $ do
    tell "------------------------------------------------\n"
    tell $ "Universal Programs:\n" ++ (show aProgs) ++   "\n"
    tell "------------------------------------------------\n"
    tell $ "Existential Programs:\n" ++ (show eProgs) ++ "\n"
    tell "------------------------------------------------\n"
    (result, trace) <- lift $ verifier $ (,) specs <$> mkRHLETrip pre aProgs eProgs post
    tell $ "Verification Trace:\n" ++ ppVTrace trace ++ "\n"
    tell "------------------------------------------------\n"
    case result of
      Right message -> tell $ "VALID. " ++ message ++ "\n"
      Left  reason  -> tell $ "INVALID. " ++ reason ++ "\n"
    tell "------------------------------------------------"
  return result

rhleVerifier :: Verifier
rhleVerifier specs_trip = runWriterT $ do
  let vcs = S.packageSmt $ do
        (specs, RHLETrip pre aProgs eProgs post) <- specs_trip
        vcsE    <- generateVCList eProgs post VCExistential $ especs specs
        post'   <- S.simplify =<< S.mkAnd vcsE
        vcsA    <- generateVCList aProgs post' VCUniversal $ aspecs specs
        vcsConj <- S.mkAnd vcsA
        S.mkImplies pre vcsConj
  logMsg  $ "Verification Conditions\n" ++ (indent (S.dumpExpr vcs)) ++ "\n"
  (maybeModel) <- lift $ S.checkValid vcs
  case maybeModel of
    Nothing -> return.Right $ ""
    Just model ->
      let modelStr = S.modelToString model
      in return.Left $ "Model:\n" ++ (sortAndIndent $ modelStr)
  where
    indent = intercalate "\n" . (map $ \l -> "  " ++ l) . lines
    sortAndIndent = intercalate "\n" . (map $ \l -> "  " ++ l) . sort . lines

generateVCList :: [Prog] -> S.Expr -> VCQuant -> ASTFunSpecMap
               -> S.SMT [S.Expr]
generateVCList progs post quant funSpec =
  foldM vcFolder [post] progs
  where
    vcFolder vcs prog = do
      post' <- S.simplify =<< S.mkAnd vcs
      generateVCs prog post' quant funSpec

generateVCs :: Stmt -> S.Expr -> VCQuant -> ASTFunSpecMap
            -> S.SMT [S.Expr]
generateVCs stmt post quant specs = case stmt of
  SSkip       -> return [post]
  SSeq []     -> generateVCs SSkip post quant specs
  SSeq (s:ss) -> do
    post' <- generateVCs (SSeq ss) post quant specs >>= S.mkAnd
    generateVCs s post' quant specs
  SAsgn lhs rhs -> do
    subPost <- subAexp post lhs rhs
    return [subPost]
  SIf b s1 s2 -> do
    cond   <- bexpToZ3 b
    ncond  <- S.mkNot cond
    vcs1   <- generateVCs s1 post quant specs
    vcs2   <- generateVCs s2 post quant specs
    vcIf   <- S.mkImplies cond  =<< S.mkAnd vcs1
    vcElse <- S.mkImplies ncond =<< S.mkAnd vcs2
    vc     <- S.mkAnd [vcIf, vcElse]
    return [vc]
  loop@(SWhile c body (inv, var, _)) -> do
    let progVarStrs    = Set.toList $ svars loop
    originalStateASTs <- S.mkFreshIntVars progVarStrs
    let originalStateVars = map S.exprToString originalStateASTs
    originalStateApps <- S.stringsToApps originalStateVars
    let original ast   = S.substituteByName ast progVarStrs originalStateVars

    cond        <- bexpToZ3 c
    ncond       <- S.mkNot cond
    condAndInv  <- S.mkAnd [cond,  inv]
    ncondAndInv <- S.mkAnd [ncond, inv]
    bodyVCs <- (case quant of
      VCUniversal -> do
        generateVCs body inv quant specs
      VCExistential -> do
        originalVar <- original var
        varCond     <- S.mkLt var originalVar
        bodyPost    <- S.mkAnd [inv, varCond]
        generateVCs body bodyPost quant specs)
    loopVC <- S.mkForallConst originalStateApps
              =<< original =<< S.mkImplies condAndInv =<< S.mkAnd bodyVCs
    endVC  <- S.mkForallConst originalStateApps
               =<< original =<< S.mkImplies ncondAndInv post
    return [inv, loopVC, endVC]

  SCall assignees cparams funName -> do
    spec <- specAtCallsite assignees cparams funName specs
    case spec of
      Nothing -> fail $ "No " ++ (show quant) ++ " specification for " ++ funName ++
             ". Specified functions are: " ++ (show $ funList specs)
      Just (tvars, fPre, fPost) ->
        case quant of
          VCUniversal -> do
            postImp <- S.mkImplies fPost post
            vc      <- S.mkAnd [fPre, postImp]
            return [vc]
          VCExistential -> do
            frAsgnAsts   <- mapM S.mkFreshIntVar assignees
            frAsgnApps   <- mapM S.toApp frAsgnAsts
            frPost       <- S.substitute post assignees frAsgnAsts
            frFPost      <- S.substitute fPost assignees frAsgnAsts
            existsPost   <- S.mkExistsConst frAsgnApps frFPost
            forallPost   <- S.mkForallConst frAsgnApps =<< S.mkImplies frFPost frPost
            let vcs = [fPre, existsPost, forallPost]
            S.stringsToApps tvars >>= \tvarApps ->
              case tvarApps of
                [] -> return vcs
                _  -> do
                  quantVcs <- S.mkExistsConst tvarApps =<< S.mkAnd vcs
                  return [quantVcs]
