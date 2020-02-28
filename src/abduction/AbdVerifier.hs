module AbdVerifier
  ( singleAbdVerifier
  ) where

import Abduction
import Control.Monad.Writer
import Data.List(intercalate, sort)
import qualified Data.Set as Set
import Imp
import InterpMap
import Spec
import Triples
import Verifier
import VerifierTrace
import Z3.Monad
import Z3Util

data VCQuant = VCUniversal | VCExistential

singleAbdVerifier :: Verifier
singleAbdVerifier specs (RHLETrip pre aProgs eProgs post) = runWriterT $ do
  (vcsE, abdsE)   <- lift $ generateVCList eProgs post VCExistential (especs specs)
  post'           <- lift $ simplify =<< mkAnd vcsE
  (vcsA, abdsA)   <- lift $ generateVCList aProgs post' VCUniversal (aspecs specs)
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
      return.Right $ "VALID iff the following specifications hold:\n"
        ++ (intercalate "\n" interpLines) ++ "\n"

generateVCList :: [Prog] -> AST -> VCQuant -> ASTFunSpecMap
               -> Z3 ([AST], (Set.Set Abducible))
generateVCList progs post quant funSpec =
  foldM vcFolder ([post], Set.empty) progs
  where
    vcFolder (vcs, abds) prog = do
      post' <- simplify =<< mkAnd vcs
      (vcs', abds') <- generateVCs prog post' quant funSpec
      return (vcs', Set.union abds abds')

generateVCs :: Stmt -> AST -> VCQuant -> ASTFunSpecMap
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
  loop@(SWhile c body (inv, var, _)) -> do
    let progVarStrs = Set.toList $ svars loop
    progVars            <- stringsToApps progVarStrs
    cond                <- bexpToZ3 c
    ncond               <- mkNot cond
    condAndInv          <- mkAnd [cond,  inv]
    ncondAndInv         <- mkAnd [ncond, inv]
    case quant of
      VCUniversal -> do
        (bodyVCs, abdsBody) <- generateVCs body inv quant funs
        loopVC <- mkForallConst [] progVars
                  =<< mkImplies condAndInv =<< mkAnd bodyVCs
        endVC  <- mkForallConst [] progVars
                  =<< mkImplies ncondAndInv post
        return ([inv, loopVC, endVC], abdsBody)
      VCExistential -> do
        (bodyVCs, abdsBody) <- generateVCs body inv quant funs
        loopVC <- mkForallConst [] progVars
                  =<< mkImplies condAndInv =<< mkAnd bodyVCs
        endVC  <- mkForallConst [] progVars
                  =<< mkImplies ncondAndInv post
        return ([inv, loopVC, endVC], abdsBody)
  SCall assignees fparams fname ->
    case quant of
      VCUniversal -> do
        (_, fPre, fPost, abds) <- specOrAbducibles assignees params fname funs
        postImp <- mkImplies fPost post
        vc      <- mkAnd [fPre, postImp]
        return ([vc], abds)
      VCExistential -> do
        asgnAsts     <- mapM (\a -> do mkIntVar =<< mkStringSymbol a) assignees
        frAsgnAsts   <- mapM mkFreshIntVar assignees
        frAsgnVars   <- mapM astToString frAsgnAsts
        frAsgnApps   <- mapM toApp frAsgnAsts
        (tvars, fPre, fPost, abds) <- specOrAbducibles frAsgnVars f funs
        frPost       <- substitute post asgnAsts frAsgnAsts
        frFPost      <- substitute fPost asgnAsts frAsgnAsts
        existsPost   <- mkExistsConst [] frAsgnApps frFPost
        forallPost   <- mkForallConst [] frAsgnApps =<< mkImplies frFPost frPost
        let vcs = [fPre, existsPost, forallPost]
        stringsToApps tvars >>= \tvarApps ->
          case tvarApps of
            [] -> return (vcs, abds)
            _  -> do
              quantVcs <- mkExistsConst [] tvarApps =<< mkAnd vcs
              return ([quantVcs], abds)

specOrAbducibles :: [Var] -> [Var] -> String -> ASTFunSpecMap
                 -> Z3 ([Var], AST, AST, Set.Set Abducible)
specOrAbducibles assignees params fname spec =
  case lookupFunSpec fun spec of
      Just (tvars, pre, post) -> return (tvars, pre, post, Set.empty)
      Nothing -> do
        fPreAbd  <- mkBoolVar =<< mkStringSymbol fPreVar
        fPostAbd <- mkBoolVar =<< mkStringSymbol fPostVar
        return ([], fPreAbd, fPostAbd, Set.fromList
                [ Abducible fPreVar args
                , Abducible fPostVar $ assignees ++ args ])
          where
            fPreVar  = name ++ "_pre"
            fPostVar = name ++ "_post"
