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
import Z3.Monad
import Z3Util

type ErrorMsg = String
type SuccessMsg = String

type Verifier       = FunSpecMaps -> RHLETrip -> Z3 VerifierResult
type VerifierResult = (Either ErrorMsg SuccessMsg, [VerifierTrace])

data VCQuant = VCUniversal | VCExistential deriving Show

runVerifier :: Verifier
               -> FunSpecMaps
               -> String -> [Prog] -> [Prog] -> String
               -> IO String
runVerifier verifier specs pre aProgs eProgs post = do
  (_, result) <- evalZ3 . runWriterT $ do
    tell "------------------------------------------------\n"
    tell $ "Universal Programs:\n" ++ (show aProgs) ++   "\n"
    tell "------------------------------------------------\n"
    tell $ "Existential Programs:\n" ++ (show eProgs) ++ "\n"
    tell "------------------------------------------------\n"
    trip            <- lift $ mkRHLETrip pre aProgs eProgs post
    (result, trace) <- lift $ verifier specs trip
    traceStr        <- lift $ ppVTrace trace
    tell $ "Verification Trace:\n" ++ traceStr ++ "\n"
    tell "------------------------------------------------\n"
    case result of
      Right message -> tell $ "VALID. " ++ message ++ "\n"
      Left  reason  -> tell $ "INVALID. " ++ reason ++ "\n"
    tell "------------------------------------------------"
  return result

rhleVerifier :: Verifier
rhleVerifier specs (RHLETrip pre aProgs eProgs post) = runWriterT $ do
  vcsE    <- lift $ generateVCList eProgs post VCExistential $ especs specs
  post'   <- lift $ simplify =<< mkAnd vcsE
  vcsA    <- lift $ generateVCList aProgs post' VCUniversal $ aspecs specs
  vcsConj <- lift $ mkAnd vcsA
  vcs     <- lift $ mkImplies pre vcsConj
  vcsStr  <- lift $ astToString vcs
  logMsg  $ "Verification Conditions\n" ++ (indent vcsStr) ++ "\n"
  (valid, model) <- lift $ checkValid vcs
  if valid
    then return.Right $ ""
    else do
      modelStr <- lift $ maybeModelToString model
      return.Left $ "Model:\n" ++ (sortAndIndent $ modelStr)
  where
    indent = intercalate "\n" . (map $ \l -> "  " ++ l) . lines
    sortAndIndent = intercalate "\n" . (map $ \l -> "  " ++ l) . sort . lines

generateVCList :: [Prog] -> AST -> VCQuant -> ASTFunSpecMap
               -> Z3 [AST]
generateVCList progs post quant funSpec =
  foldM vcFolder [post] progs
  where
    vcFolder vcs prog = do
      post' <- simplify =<< mkAnd vcs
      generateVCs prog post' quant funSpec

generateVCs :: Stmt -> AST -> VCQuant -> ASTFunSpecMap
            -> Z3 [AST]
generateVCs stmt post quant specs = case stmt of
  SSkip       -> return [post]
  SSeq []     -> generateVCs SSkip post quant specs
  SSeq (s:ss) -> do
    post' <- generateVCs (SSeq ss) post quant specs >>= mkAnd
    generateVCs s post' quant specs
  SAsgn lhs rhs -> do
    subPost <- subAexp post (AVar lhs) rhs
    return [subPost]
  SIf b s1 s2 -> do
    cond   <- bexpToZ3 b
    ncond  <- mkNot cond
    vcs1   <- generateVCs s1 post quant specs
    vcs2   <- generateVCs s2 post quant specs
    vcIf   <- mkImplies cond  =<< mkAnd vcs1
    vcElse <- mkImplies ncond =<< mkAnd vcs2
    vc     <- mkAnd [vcIf, vcElse]
    return [vc]
  loop@(SWhile c body (inv, var, _)) -> do
    let progVarStrs = Set.toList $ svars loop
    progVars            <- stringsToApps progVarStrs
    cond                <- bexpToZ3 c
    ncond               <- mkNot cond
    condAndInv          <- mkAnd [cond,  inv]
    ncondAndInv         <- mkAnd [ncond, inv]
    case quant of
      VCUniversal -> do
        bodyVCs <- generateVCs body inv quant specs
        loopVC  <- mkForallConst [] progVars
                   =<< mkImplies condAndInv =<< mkAnd bodyVCs
        endVC   <- mkForallConst [] progVars
                   =<< mkImplies ncondAndInv post
        return [inv, loopVC, endVC]
      VCExistential -> do
        originalStateASTs <- mkFreshIntVars progVarStrs
        originalStateVars <- mapM astToString originalStateASTs
        originalStateApps <- stringsToApps originalStateVars
        let original ast   = substituteByName ast progVarStrs originalStateVars

        originalVar <- original var
        varCond     <- mkLt var originalVar
        bodyPost    <- mkAnd [inv, varCond]
        bodyVCs     <- generateVCs body bodyPost quant specs

        loopVC <- mkForallConst [] originalStateApps
                  =<< original =<< mkImplies condAndInv =<< mkAnd bodyVCs
        endVC  <- mkForallConst [] originalStateApps
                  =<< original =<< mkImplies ncondAndInv post
        return [inv, loopVC, endVC]
  SCall assignees cparams funName -> do
    spec <- specAtCallsite assignees cparams funName specs
    case spec of
      Nothing -> fail $ "No " ++ (show quant) ++ " specification for " ++ funName ++
             ". Specified functions are: " ++ (show $ funList specs)
      Just (tvars, fPre, fPost) ->
        case quant of
          VCUniversal -> do
            postImp <- mkImplies fPost post
            vc      <- mkAnd [fPre, postImp]
            return [vc]
          VCExistential -> do
            asgnAsts     <- mapM (\a -> do mkIntVar =<< mkStringSymbol a) assignees
            frAsgnAsts   <- mapM mkFreshIntVar assignees
            frAsgnApps   <- mapM toApp frAsgnAsts
            frPost       <- substitute post asgnAsts frAsgnAsts
            frFPost      <- substitute fPost asgnAsts frAsgnAsts
            existsPost   <- mkExistsConst [] frAsgnApps frFPost
            forallPost   <- mkForallConst [] frAsgnApps =<< mkImplies frFPost frPost
            let vcs = [fPre, existsPost, forallPost]
            stringsToApps tvars >>= \tvarApps ->
              case tvarApps of
                [] -> return vcs
                _  -> do
                  quantVcs <- mkExistsConst [] tvarApps =<< mkAnd vcs
                  return [quantVcs]
