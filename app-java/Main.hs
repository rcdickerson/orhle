import           Control.Applicative            ( liftA2 )
import           Control.Arrow                  ( left )
import           Control.Monad.Except           ( ExceptT
                                                , liftEither
                                                , liftIO
                                                , liftM2
                                                , liftM4
                                                , runExceptT
                                                , throwError
                                                )
import           Control.Monad.State            ( evalStateT
                                                , get
                                                , lift
                                                , put
                                                )
import           Data.Functor.Compose           ( Compose(..) )
import           Data.Map                       ( Map )
import qualified Data.Map                      as Map
import qualified Data.Map.Merge.Lazy           as Map
import qualified Data.Text.IO                  as TIO
import           System.IO                      ( hPrint
                                                , hPutStrLn
                                                , stderr
                                                )
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           System.FilePath                ( replaceFileName )

import qualified Language.Java.Parser          as JavaParser
import qualified Language.Java.Syntax          as JavaSyntax

import           Orhle
import           Orhle.Imp
import           Orhle.ImpPrettyPrint
import qualified Orhle.SMT                     as S

import           Translate
import           VerificationTaskParser

type App = ExceptT String IO
type JavaProg = JavaSyntax.CompilationUnit

main :: IO ()
main = do
  print "Dead implementation"
-- main = (>>= reportResult) $ runExceptT $ do
--   args                    <- liftIO getArgs
--   (vtFilePath, specPaths) <- parseArgs args
--   verifTask               <- parseFile parseVerificationTask vtFilePath
--   liftIO $ hPrint stderr verifTask

--   funSpecsLists <- mapM (parseFile parseFunSpecsFile) specPaths
--   let funSpecs = both (Map.fromList . concat) (unzip funSpecsLists)

--   javaPrograms <- readAllPrograms
--     vtFilePath
--     (vtForallExecs verifTask, vtExistsExecs verifTask)
--   let methCtxts = createMethodContexts verifTask
--       lookupMethCtxt k =
--         Map.findWithDefault (MethodContext Map.empty Map.empty) k methCtxts
--   impPrograms <- liftEither $ forBothA javaPrograms $ mapM $ \(exec, prog) ->
--     (,) exec <$> translate (lookupMethCtxt exec) prog
--   _ <- forBothA impPrograms $ mapM $ \(name, prog) -> do
--     liftIO $ hPrint stderr name
--     liftIO $ TIO.hPutStrLn stderr $ prettyprint prog

--   z3PreCond            <- liftEitherShow $ parseSMT $ vtPreCond verifTask
--   z3PostCond           <- liftEitherShow $ parseSMT $ vtPostCond verifTask
--   z3FunSpecs           <- forBothA funSpecs (liftEitherShow . stringToASTSpec)
--   (z3AProgs, z3EProgs) <- forBothA impPrograms $ mapM $ \(name, prog) -> do
--     z3prog <- liftEitherShow $ parseLoopSpecs prog
--     return $ prefixProgVars (execution2prefix name) =<< z3prog

--   (result, trace) <- liftIO $ do
--     let funSpecMaps_trip = liftM2
--           (,)
--           (uncurry (liftM2 FunSpecMaps) z3FunSpecs)
--           (liftM4 RHLETrip
--                   z3PreCond
--                   (sequence z3AProgs)
--                   (sequence z3EProgs)
--                   z3PostCond
--           )
--     (result, trace) <- rhleVerifier funSpecMaps_trip
--     let traceStr = ppVTrace trace

--     return (result, traceStr)
--   liftIO $ case result of
--     Left  e -> putStrLn ("INVALID: " ++ e)
--     Right _ -> putStrLn "VALID"
--   liftIO $ putStrLn $ "TRACE:\n" ++ trace
--   return ()
--  where
--   reportResult (Left  err) = putStrLn $ "Error: " ++ err
--   reportResult (Right () ) = return ()

-- parseArgs :: [String] -> App (FilePath, [FilePath])
-- parseArgs (filePath : specPaths) = return (filePath, specPaths)
-- parseArgs [] = liftIO showUsage >> throwError "no filename provided"

-- parseFile :: (Show e) => (String -> Either e a) -> FilePath -> App a
-- parseFile parser filePath = do
--   fileContents <- liftIO $ readFile filePath
--   liftEitherShow $ parser fileContents

-- showUsage :: IO ()
-- showUsage = do
--   progName <- getProgName
--   putStrLn
--     $  "Usage: "
--     ++ progName
--     ++ " <verificationTask.jklive> <functionSpecifications.jklspec>..."

-- readAllPrograms
--   :: FilePath
--   -> ([Execution], [Execution])
--   -> App ([(Execution, JavaProg)], [(Execution, JavaProg)])
-- readAllPrograms vtFilePath progs =
--   flip evalStateT Map.empty
--     $ forBothA progs
--     $ mapM
--     $ \exec@(Execution name _) -> do
--         cache          <- get
--         (prog, cache') <- lookupOrInsertA
--           (lift (readJavaFile vtFilePath name))
--           name
--           cache
--         put cache'
--         return (exec, prog)

-- readJavaFile :: String -> String -> App JavaProg
-- readJavaFile vtFilePath programName = do
--   let filePath = replaceFileName vtFilePath (programName ++ ".java")
--   fileContents <- liftIO $ readFile filePath
--   liftEither
--     $ left ((("could not parse Java file `" ++ filePath ++ "`:\n") ++) . show)
--     $ JavaParser.parser JavaParser.compilationUnit fileContents

-- createMethodContexts :: VerificationTask -> Map Execution MethodContext
-- createMethodContexts (VerificationTask _ _ _ _ invars vars) = Map.merge
--   (Map.mapMissing (\_ m -> MethodContext m Map.empty))
--   (Map.mapMissing (\_ m -> MethodContext Map.empty m))
--   (Map.zipWithMatched (const MethodContext))
--   (toMap invars)
--   (toMap vars)
--  where
--   toMap = foldr
--     (\(exec, label, s) -> Map.insertWith Map.union exec (Map.singleton label s))
--     Map.empty

-- -- TODO: duplicated from KLiveParser
-- execution2prefix :: Execution -> String
-- execution2prefix (Execution name Nothing   ) = name ++ "!"
-- execution2prefix (Execution name (Just sub)) = name ++ "!" ++ sub ++ "!"

-- -- TODO: duplicated from KLiveParser
-- prefixProgVars :: String -> Stmt -> S.SMT Stmt
-- prefixProgVars pre prog = case prog of
--   SSkip          -> return SSkip
--   SAsgn var aexp -> return $ SAsgn (pre ++ var) (prefixA aexp)
--   SSeq stmts     -> do
--     pstmts <- mapM (prefixProgVars pre) stmts
--     return $ SSeq pstmts
--   SIf cond s1 s2 -> do
--     ps1 <- prefixProgVars pre s1
--     ps2 <- prefixProgVars pre s2
--     return $ SIf (prefixB cond) ps1 ps2
--   SWhile cond body (inv, var, local) -> do
--     pinv  <- prefixASTVars pre inv
--     pvar  <- prefixASTVars pre var
--     pbody <- prefixProgVars pre body
--     return $ if local
--       then SWhile (prefixB cond) pbody (pinv, pvar, local)
--       else SWhile (prefixB cond) pbody (inv, pvar, local)
--   SCall rets params fname ->
--     return $ SCall (map prefix rets) (map prefix params) fname
--  where
--   prefix s = pre ++ s
--   prefixA = prefixAExpVars pre
--   prefixB = prefixBExpVars pre

-- -- Generic Utilities

-- both :: (a -> b) -> (a, a) -> (b, b)
-- both f (a, b) = (f a, f b)

-- forBothA :: Applicative f => (a, a) -> (a -> f b) -> f (b, b)
-- forBothA (a, b) f = liftA2 (,) (f a) (f b)

-- liftEitherShow :: (Show e) => Either e a -> App a
-- liftEitherShow = liftEither . left show

-- lookupOrInsertA
--   :: (Applicative f, Ord k) => f a -> k -> Map k a -> f (a, Map k a)
-- lookupOrInsertA fa k =
--   getCompose . Map.alterF (Compose . maybe (fmap g fa) (pure . g)) k
--   where g a = (a, Just a)
