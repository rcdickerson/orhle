import           Control.Arrow                  ( left )
import           Control.Monad.Except           ( ExceptT
                                                , forM
                                                , forM_
                                                , liftEither
                                                , liftIO
                                                , runExceptT
                                                , throwError
                                                )
import           Data.Map.Strict                ( (!) )
import qualified Data.Map.Strict               as Map
import qualified Data.Set                      as Set
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           System.FilePath                ( replaceFileName )

import qualified Language.Java.Parser          as JavaParser
import qualified Language.Java.Syntax          as JavaSyntax
import           Translate
import           VerificationTaskParser

main :: IO ()
main = (>>= reportResult) $ runExceptT $ do
  args           <- liftIO getArgs
  vtFilePath     <- parseArgs args
  vtFileContents <- liftIO $ readFile vtFilePath
  verifTask <- liftEither $ left show $ parseVerificationTask vtFileContents
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
    liftIO $ print prog
 where
  reportResult (Left  err) = putStrLn $ "Error: " ++ err
  reportResult (Right () ) = return ()

parseArgs :: [String] -> ExceptT String IO FilePath
parseArgs [filePath] = return filePath
parseArgs _          = liftIO showUsage >> throwError "no filename provided"

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
