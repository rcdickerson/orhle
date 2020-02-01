import           Data.String                    ( fromString )
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           Control.Monad.Except           ( ExceptT
                                                , runExceptT
                                                , liftIO
                                                , liftEither
                                                , throwError
                                                , forM_
                                                )
import           Control.Arrow                  ( left )
import           System.FilePath                ( replaceFileName )
import qualified Data.Set                      as Set
import qualified Data.Map.Strict               as Map

import qualified Language.Java.Parser          as JavaParser
import qualified Language.Java.Syntax          as JavaSyntax
import           VerificationTaskParser
import           Translate

main :: IO ()
main = (>>= reportResult) $ runExceptT $ do
  args           <- liftIO getArgs
  vtFilePath     <- parseArgs args
  vtFileContents <- liftIO $ readFile vtFilePath
  verifTask <- liftEither $ left show $ parseVerificationTask vtFileContents
  liftIO $ print verifTask
  let programNames =
        Set.fromList
          . map execProgramName
          $ (vtForallExecs verifTask ++ vtExistsExecs verifTask)
  javaPrograms <- sequence $ Map.fromSet (readJavaFile vtFilePath) programNames
  impPrograms <- liftEither $ mapM translate javaPrograms
  forM_ (Map.toList impPrograms) $ \(name, prog) -> do
    liftIO $ putStrLn name
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
