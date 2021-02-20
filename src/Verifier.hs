module Verifier
  ( Verifier
  , VerifierResult
  , rhleVerifier
  , runVerifier
  ) where

import           Control.Monad.Writer
import           Data.List             ( intercalate
                                       , sort
                                       )
import qualified Data.Set             as Set
import           Imp
import           Spec
import           SMTMonad              ( SMT )
import qualified SMTMonad             as SMT
import           Triples
import           VerifierTrace

type Verifier       = SMT (FunSpecMaps, RHLETrip) -> IO VerifierResult
type VerifierResult = (Either ErrorMsg SuccessMsg, [VerifierTrace])

type ErrorMsg   = String
type SuccessMsg = String

data VCQuant = VCUniversal
             | VCExistential
             deriving Show

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
  let vcs = SMT.packageSmt $ do
        (specs, RHLETrip pre aProgs eProgs post) <- specs_trip
        vcsE    <- generateVCList eProgs post VCExistential $ especs specs
        post'   <- SMT.simplify =<< SMT.mkAnd vcsE
        vcsA    <- generateVCList aProgs post' VCUniversal $ aspecs specs
        vcsConj <- SMT.mkAnd vcsA
        SMT.mkImplies pre vcsConj
  logMsg  $ "Verification Conditions\n" ++ (indent (SMT.dumpExpr vcs)) ++ "\n"
  (maybeModel) <- lift $ SMT.checkValid vcs
  case maybeModel of
    Nothing -> return.Right $ ""
    Just model ->
      let modelStr = SMT.modelToString model
      in return.Left $ "Model:\n" ++ (sortAndIndent $ modelStr)
  where
    indent = intercalate "\n" . (map $ \l -> "  " ++ l) . lines
    sortAndIndent = intercalate "\n" . (map $ \l -> "  " ++ l) . sort . lines

generateVCList :: [Prog] -> SMT.Expr -> VCQuant -> ASTFunSpecMap
               -> SMT [SMT.Expr]
generateVCList progs post quant funSpec =
  foldM vcFolder [post] progs
  where
    vcFolder vcs prog = do
      post' <- SMT.simplify =<< SMT.mkAnd vcs
      generateVCs prog post' quant funSpec

generateVCs :: Stmt -> SMT.Expr -> VCQuant -> ASTFunSpecMap
            -> SMT [SMT.Expr]
generateVCs stmt post quant specs = case stmt of
  SSkip       -> return [post]
  SSeq []     -> generateVCs SSkip post quant specs
  SSeq (s:ss) -> do
    post' <- generateVCs (SSeq ss) post quant specs >>= SMT.mkAnd
    generateVCs s post' quant specs
  SAsgn lhs rhs -> do
    subPost <- subAexp post lhs rhs
    return [subPost]
  SIf b s1 s2 -> do
    cond   <- bexpToZ3 b
    ncond  <- SMT.mkNot cond
    vcs1   <- generateVCs s1 post quant specs
    vcs2   <- generateVCs s2 post quant specs
    vcIf   <- SMT.mkImplies cond  =<< SMT.mkAnd vcs1
    vcElse <- SMT.mkImplies ncond =<< SMT.mkAnd vcs2
    vc     <- SMT.mkAnd [vcIf, vcElse]
    return [vc]
  loop@(SWhile c body (inv, var, _)) -> do
    let progVarStrs    = Set.toList $ svars loop
    originalStateASTs <- SMT.mkFreshIntVars progVarStrs
    let originalStateVars = map SMT.exprToString originalStateASTs
    originalStateApps <- SMT.stringsToApps originalStateVars
    let original ast   = SMT.substituteByName ast progVarStrs originalStateVars

    cond        <- bexpToZ3 c
    ncond       <- SMT.mkNot cond
    condAndInv  <- SMT.mkAnd [cond,  inv]
    ncondAndInv <- SMT.mkAnd [ncond, inv]
    bodyVCs <- (case quant of
      VCUniversal -> do
        generateVCs body inv quant specs
      VCExistential -> do
        originalVar <- original var
        varCond     <- SMT.mkLt var originalVar
        bodyPost    <- SMT.mkAnd [inv, varCond]
        generateVCs body bodyPost quant specs)
    loopVC <- SMT.mkForallConst originalStateApps
              =<< original =<< SMT.mkImplies condAndInv =<< SMT.mkAnd bodyVCs
    endVC  <- SMT.mkForallConst originalStateApps
               =<< original =<< SMT.mkImplies ncondAndInv post
    return [inv, loopVC, endVC]

  SCall assignees cparams funName -> do
    spec <- specAtCallsite assignees cparams funName specs
    case spec of
      Nothing -> fail $ "No " ++ (show quant) ++ " specification for " ++ funName ++
             ". Specified functions are: " ++ (show $ funList specs)
      Just (tvars, fPre, fPost) ->
        case quant of
          VCUniversal -> do
            postImp <- SMT.mkImplies fPost post
            vc      <- SMT.mkAnd [fPre, postImp]
            return [vc]
          VCExistential -> do
            frAsgnAsts   <- mapM SMT.mkFreshIntVar assignees
            frAsgnApps   <- mapM SMT.toApp frAsgnAsts
            frPost       <- SMT.substitute post assignees frAsgnAsts
            frFPost      <- SMT.substitute fPost assignees frAsgnAsts
            existsPost   <- SMT.mkExistsConst frAsgnApps frFPost
            forallPost   <- SMT.mkForallConst frAsgnApps =<< SMT.mkImplies frFPost frPost
            let vcs = [fPre, existsPost, forallPost]
            SMT.stringsToApps tvars >>= \tvarApps ->
              case tvarApps of
                [] -> return vcs
                _  -> do
                  quantVcs <- SMT.mkExistsConst tvarApps =<< SMT.mkAnd vcs
                  return [quantVcs]
