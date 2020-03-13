import           Control.Arrow                  ( left )
import           Control.Monad.Except           ( ExceptT
                                                , forM
                                                , forM_
                                                , liftEither
                                                , liftIO
                                                , runExceptT
                                                , throwError
                                                )
import           Data.Map                       ( (!) )
import qualified Data.Map                      as Map
import qualified Data.Set                      as Set
import qualified Data.Text.IO                  as TIO
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           System.FilePath                ( replaceFileName )

import qualified Language.Java.Parser          as JavaParser
import qualified Language.Java.Syntax          as JavaSyntax

import           ImpPrettyPrint
import           Spec                           ( stringToASTSpec )

import           Translate
import           VerificationTaskParser

main :: IO ()
main = (>>= reportResult) $ runExceptT $ do
  args                    <- liftIO getArgs
  (vtFilePath, specPaths) <- parseArgs args
  verifTask               <- parseFile parseVerificationTask vtFilePath
  funSpecsLists           <- mapM (parseFile parseFunSpecsFile) specPaths
  let (aFunSpecs, eFunSpecs) =
        both (Map.fromList . concat) (unzip funSpecsLists)
  liftIO $ print verifTask
  let allExecs     = vtForallExecs verifTask ++ vtExistsExecs verifTask
  let programNames = Set.fromList (map execProgramName allExecs)
  javaPrograms <- sequence $ Map.fromSet (readJavaFile vtFilePath) programNames
  impExecs     <- liftEither $ forM allExecs $ \exec ->
    let extract f =
            Map.fromList
              . map (\(_, x, y) -> (x, y))
              . filter (\(e, _, _) -> e == exec)
              $ f verifTask
        mc = MethodContext (extract vtLoopInvariants) (extract vtLoopVariants)
    in  (,) exec <$> translate mc (javaPrograms ! execProgramName exec)
  forM_ impExecs $ \(name, prog) -> do
    liftIO $ print name
    liftIO $ TIO.putStrLn $ prettyprint prog
  _aZ3FunSpecs <- liftEither $ left show $ stringToASTSpec aFunSpecs
  _eZ3FunSpecs <- liftEither $ left show $ stringToASTSpec eFunSpecs
  return ()
 where
  reportResult (Left  err) = putStrLn $ "Error: " ++ err
  reportResult (Right () ) = return ()

parseArgs :: [String] -> ExceptT String IO (FilePath, [FilePath])
parseArgs (filePath : specPaths) = return (filePath, specPaths)
parseArgs [] = liftIO showUsage >> throwError "no filename provided"

parseFile
  :: (Show e) => (String -> Either e a) -> FilePath -> ExceptT String IO a
parseFile parser filePath = do
  fileContents <- liftIO $ readFile filePath
  liftEither $ left show $ parser fileContents

showUsage :: IO ()
showUsage = do
  progName <- getProgName
  putStrLn ("Usage: " ++ progName ++ " <verificationTask.jklive>")

readJavaFile :: String -> String -> ExceptT String IO JavaSyntax.CompilationUnit
readJavaFile vtFilePath programName = do
  let filePath = replaceFileName vtFilePath (programName ++ ".java")
  fileContents <- liftIO $ readFile filePath
  liftEither
    $ left ((("could not parse Java file `" ++ filePath ++ "`:\n") ++) . show)
    $ JavaParser.parser JavaParser.compilationUnit fileContents

both :: (a -> b) -> (a, a) -> (b, b)
both f (a, b) = (f a, f b)
