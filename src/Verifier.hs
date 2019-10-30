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
import Data.List(intercalate)
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

noAbdVerifier :: ASTSpec -> RHLETrip -> Z3 (VResult, [VTrace])
noAbdVerifier spec trip = runWriterT $ verifyNoAbd spec trip

verifyNoAbd :: ASTSpec -> RHLETrip -> VTracedResult
verifyNoAbd spec (RHLETrip pre aProgs eProgs post) = do
  (vcsE, abdsE)  <- lift $ generateVCList eProgs post VCExistential spec
  post'          <- lift $ simplify =<< mkAnd vcsE
  (vcsA, abdsA)  <- lift $ generateVCList aProgs post' VCUniversal spec
  let combinedAbds = Set.union abdsE abdsA
  if not $ Set.null combinedAbds then
    return.Left $ "Missing specifications: " ++ (abdNameList combinedAbds)
    else do
      vcsConj <- lift $ mkAnd vcsA
      vcs     <- lift $ mkImplies pre vcsConj
      vcsStr  <- lift $ astToString vcs
      logMsg  $ "Verification Conditions\n" ++ (indent vcsStr)
      valid   <- lift $ checkValid =<< mkImplies pre vcs
      if valid
        then return.Right $ emptyIMap
        else do
          model <- lift $ getModelAsString =<< mkNot vcs
          return.Left $ "Invalid Verification Conditions\nModel:\n" ++ (indent model)
  where
    abdNameList abds = show . Set.toList $ Set.map abdName abds
    indent = concat . (map $ \l -> "  " ++ l ++ "\n") . lines

singleAbdVerifier :: RHLETrip -> Z3 (VResult, [VTrace])
singleAbdVerifier trip = runWriterT $ verifySingleAbd trip

verifySingleAbd :: RHLETrip -> VTracedResult
verifySingleAbd (RHLETrip pre aProgs eProgs post) = do
  (vcsE, abdsE)   <- lift $ generateVCList eProgs post VCExistential emptyASTSpec
  post'           <- lift $ simplify =<< mkAnd vcsE
  (vcsA, abdsA)   <- lift $ generateVCList aProgs post' VCUniversal emptyASTSpec
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

generateVCList :: [Prog] -> AST -> VCQuant -> ASTSpec -> Z3 ([AST], (Set.Set Abducible))
generateVCList progs post quant spec =
  foldM (vcFolder quant spec) ([post], Set.empty) progs
  where
    vcFolder quant spec (vcs, abds) prog = do
      post <- simplify =<< mkAnd vcs
      (vcs', abds') <- generateVCs prog post quant spec
      return (vcs', Set.union abds abds')

generateVCs :: Stmt -> AST -> VCQuant -> ASTSpec -> Z3 ([AST], (Set.Set Abducible))
generateVCs stmt post quant spec = case stmt of
  Skip       -> return ([post], Set.empty)
  Seq []     -> generateVCs Skip post quant spec
  Seq (s:ss) -> do
    (vcs2, abds2) <- generateVCs (Seq ss) post quant spec
    (vcs1, abds1) <- (\post' -> generateVCs s post' quant spec) =<< mkAnd vcs2
    return (vcs1, Set.union abds1 abds2)
  lhs := rhs -> do
    subPost <- subAexp post (V lhs) rhs
    return ([subPost], Set.empty)
  If b s1 s2 -> do
    cond  <- bexpToZ3 b
    ncond <- mkNot cond
    (vcs1, abds1) <- generateVCs s1 post quant spec
    (vcs2, abds2) <- generateVCs s2 post quant spec
    vcIf   <- mkImplies cond  =<< mkAnd vcs1
    vcElse <- mkImplies ncond =<< mkAnd vcs2
    vc     <- mkAnd [vcIf, vcElse]
    return ([vc], Set.union abds1 abds2)
  Call assignee f ->
    case quant of
      VCUniversal -> do
        (fPre, fPost, abds) <- specOrAbducibles assignee f spec
        postImp <- mkImplies fPost post
        vc      <- mkAnd [fPre, postImp]
        return ([vc], abds)
      VCExistential -> do
        asgnAst      <- mkIntVar =<< mkStringSymbol assignee
        frAsgnAst    <- mkFreshIntVar assignee
        frAsgnVar    <- astToString frAsgnAst
        frAsgnApp    <- toApp frAsgnAst
        (fPre, fPost, abds) <- specOrAbducibles frAsgnVar f spec
        fPostAndPost <- mkAnd [fPost, post]
        existsPost   <- mkExistsConst [] [frAsgnApp]
                        =<< substitute fPostAndPost [asgnAst] [frAsgnAst]
        vc           <- mkAnd [fPre, existsPost]
        return ([vc], abds)

specOrAbducibles :: Var -> Func -> ASTSpec -> Z3 (AST, AST, Set.Set Abducible)
specOrAbducibles assignee func@(Func name args) spec =
  case funSpec func spec of
      Just (pr, po) -> return (pr, po, Set.empty)
      Nothing -> do
        fPreAbd  <- mkBoolVar =<< mkStringSymbol fPreVar
        fPostAbd <- mkBoolVar =<< mkStringSymbol fPostVar
        return (fPreAbd, fPostAbd, Set.fromList
                [ Abducible fPreVar args
                , Abducible fPostVar $ assignee:args ])
          where
            fPreVar  = name ++ "_pre"
            fPostVar = name ++ "_post"
