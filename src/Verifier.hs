module Verifier
  ( Verifier
  , VResult
  , VTracedResult
  , noAbdVerifier
  , runVerifier
  , singleAbdVerifier
  ) where

import Abduction
import Control.Monad.Writer
import Data.List(intercalate, sort)
import qualified Data.Set as Set
import Imp
import InterpMap
import Specification
import Triples
import VTrace
import Z3.Monad
import Z3Util

type Verifier      = RHLETrip -> Z3 (VResult, [VTrace])
type VResult       = Either String InterpMap
type VTracedResult = WriterT [VTrace] Z3 VResult

data VCQuant = VCUniversal | VCExistential

runVerifier :: Verifier -> String -> [Prog] -> [Prog] -> String -> IO String
runVerifier verifier pre aProgs eProgs post = do
  (_, result) <- evalZ3 $ runWriterT $ runVerifier' verifier pre aProgs eProgs post
  return result

runVerifier' :: Verifier -> String -> [Prog] -> [Prog] -> String -> WriterT String Z3 ()
runVerifier' verifier pre aProgs eProgs post = do
  tell "------------------------------------------------\n"
  tell $ "Universal Program:\n" ++ (show aProgs) ++     "\n"
  tell "------------------------------------------------\n"
  tell $ "Existential Program:\n" ++ (show eProgs) ++   "\n"
  tell "------------------------------------------------\n"
  trip <- lift $ mkRHLETrip pre aProgs eProgs post
  (result, trace) <- lift $ verifier trip
  traceStr <- lift $ ppVTrace trace
  tell $ "Verification Trace:\n" ++ traceStr ++ "\n"
  tell "------------------------------------------------\n"
  case result of
    Right imap -> do
      tell "VALID iff the following specifications hold:\n"
      mapLines <- lift $ ppInterpMap imap
      tell $ intercalate "\n" mapLines
      tell $ "\n"
    Left reason -> do
      tell $ "INVALID: " ++ reason ++ "\n"
  tell "------------------------------------------------"

noAbdVerifier :: ASTFunSpec -> RHLETrip -> Z3 (VResult, [VTrace])
noAbdVerifier spec trip = runWriterT $ verifyNoAbd spec trip

verifyNoAbd :: ASTFunSpec -> RHLETrip -> VTracedResult
verifyNoAbd funSpec (RHLETrip pre aProgs eProgs post) = do
  (vcsE, abdsE)  <- lift $ generateVCList eProgs post VCExistential funSpec
  post'          <- lift $ simplify =<< mkAnd vcsE
  (vcsA, abdsA)  <- lift $ generateVCList aProgs post' VCUniversal funSpec
  let combinedAbds = Set.union abdsE abdsA
  if not $ Set.null combinedAbds then
    return.Left $ "Missing specifications: " ++ (abdNameList combinedAbds)
    else do
      vcsConj <- lift $ mkAnd vcsA
      vcs     <- lift $ mkImplies pre vcsConj
      vcsStr  <- lift $ astToString vcs
      logMsg  $ "Verification Conditions\n" ++ (indent vcsStr) ++ "\n"
      (valid, model) <- lift $ checkValid vcs
      if valid
        then return.Right $ emptyIMap
        else do
          modelStr <- lift $ maybeModelToString model
          return.Left $ "Model:\n" ++ (sortAndIndent $ modelStr)
  where
    abdNameList abds = show . Set.toList $ Set.map abdName abds
    indent = intercalate "\n" . (map $ \l -> "  " ++ l) . lines
    sortAndIndent = intercalate "\n" . (map $ \l -> "  " ++ l) . sort . lines

singleAbdVerifier :: RHLETrip -> Z3 (VResult, [VTrace])
singleAbdVerifier trip = runWriterT $ verifySingleAbd trip

verifySingleAbd :: RHLETrip -> VTracedResult
verifySingleAbd (RHLETrip pre aProgs eProgs post) = do
  (vcsE, abdsE)   <- lift $ generateVCList eProgs post VCExistential emptyFunSpec
  post'           <- lift $ simplify =<< mkAnd vcsE
  (vcsA, abdsA)   <- lift $ generateVCList aProgs post' VCUniversal emptyFunSpec
  let abds = Set.toList $ Set.union abdsA abdsE
  (result, trace) <- lift $ abduce abds [pre] vcsA
  logAbductionTrace trace
  preStr <- lift $ astToString pre
  vcsStr <- lift $ astToString =<< mkAnd (vcsA ++ vcsE)
  case result of
    Left reason -> do
      logAbductionFailure preStr vcsStr
      return.Left $ reason
    Right imap  -> do
      interpLines <- lift $ ppInterpMap imap
      logAbductionSuccess interpLines preStr vcsStr
      return.Right $ imap

generateVCList :: [Prog] -> AST -> VCQuant -> ASTFunSpec
               -> Z3 ([AST], (Set.Set Abducible))
generateVCList progs post quant funSpec =
  foldM vcFolder ([post], Set.empty) progs
  where
    vcFolder (vcs, abds) prog = do
      post' <- simplify =<< mkAnd vcs
      (vcs', abds') <- generateVCs prog post' quant funSpec
      return (vcs', Set.union abds abds')

generateVCs :: Stmt -> AST -> VCQuant -> ASTFunSpec
            -> Z3 ([AST], (Set.Set Abducible))
generateVCs stmt post quant funs = case stmt of
  SSkip       -> return ([post], Set.empty)
  SSeq []     -> generateVCs SSkip post quant funs
  SSeq (s:ss) -> do
    (vcs2, abds2) <- generateVCs (SSeq ss) post quant funs
    (vcs1, abds1) <- (\post' -> generateVCs s post' quant funs)
                     =<< mkAnd vcs2
    return (vcs1, Set.union abds1 abds2)
  SAsgn lhs rhs -> do
    subPost <- subAexp post (AVar lhs) rhs
    return ([subPost], Set.empty)
  SIf b s1 s2 -> do
    cond  <- bexpToZ3 b
    ncond <- mkNot cond
    (vcs1, abds1) <- generateVCs s1 post quant funs
    (vcs2, abds2) <- generateVCs s2 post quant funs
    vcIf   <- mkImplies cond  =<< mkAnd vcs1
    vcElse <- mkImplies ncond =<< mkAnd vcs2
    vc     <- mkAnd [vcIf, vcElse]
    return ([vc], Set.union abds1 abds2)
  SWhile c body (inv, var) -> do
        cond                <- bexpToZ3 c
        ncond               <- mkNot cond
        condAndInv          <- mkAnd [cond,  inv]
        ncondAndInv         <- mkAnd [ncond, inv]
        (bodyVCs, abdsBody) <- generateVCs body inv quant funs
        loopVC              <- mkImplies condAndInv =<< mkAnd bodyVCs
        endVC               <- mkImplies ncondAndInv post
        return ([inv, loopVC, endVC], abdsBody)
  SCall assignee f ->
    case quant of
      VCUniversal -> do
        (_, fPre, fPost, abds) <- specOrAbducibles assignee f funs
        postImp <- mkImplies fPost post
        vc      <- mkAnd [fPre, postImp]
        return ([vc], abds)
      VCExistential -> do
        asgnAst      <- mkIntVar =<< mkStringSymbol assignee
        frAsgnAst    <- mkFreshIntVar assignee
        frAsgnVar    <- astToString frAsgnAst
        frAsgnApp    <- toApp frAsgnAst
        (tvars, fPre, fPost, abds) <- specOrAbducibles frAsgnVar f funs
        frPost       <- substitute post [asgnAst] [frAsgnAst]
        frFPost      <- substitute fPost [asgnAst] [frAsgnAst]
        existsPost   <- mkExistsConst [] [frAsgnApp] frFPost
        forallPost   <- mkForallConst [] [frAsgnApp] =<< mkImplies frFPost frPost
        let vcs = [fPre, existsPost, forallPost]
        stringsToApps tvars >>= \tvarApps ->
          case tvarApps of
            [] -> return (vcs, abds)
            _  -> do
              quantVcs <- mkExistsConst [] tvarApps =<< mkAnd vcs
              return ([quantVcs], abds)

specOrAbducibles :: Var -> SFun -> ASTFunSpec -> Z3 ([Var], AST, AST, Set.Set Abducible)
specOrAbducibles assignee fun@(SFun name args) spec =
  case lookupFunSpec fun spec of
      Just (tvars, pre, post) -> return (tvars, pre, post, Set.empty)
      Nothing -> do
        fPreAbd  <- mkBoolVar =<< mkStringSymbol fPreVar
        fPostAbd <- mkBoolVar =<< mkStringSymbol fPostVar
        return ([], fPreAbd, fPostAbd, Set.fromList
                [ Abducible fPreVar args
                , Abducible fPostVar $ assignee:args ])
          where
            fPreVar  = name ++ "_pre"
            fPostVar = name ++ "_post"
