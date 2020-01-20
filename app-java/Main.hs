import           Data.String                    ( fromString )
import           System.Environment             ( getArgs
                                                , getProgName
                                                )
import           Control.Monad.Except           ( ExceptT
                                                , runExceptT
                                                , liftIO
                                                , liftEither
                                                , throwError
                                                )
import           Control.Arrow                  ( left )
import           System.FilePath                ( replaceFileName )
import qualified Data.Set                      as Set
import qualified Data.Map.Strict               as Map

import qualified Language.Java.Parser          as JavaParser
import qualified Language.Java.Syntax          as JavaSyntax
import           InstructionsParser

main :: IO ()
main = (>>= reportResult) $ runExceptT $ do
  args              <- liftIO getArgs
  instrFilePath     <- parseArgs args
  instrFileContents <- liftIO $ readFile instrFilePath
  instructions <- liftEither $ left show $ parseInstructions instrFileContents
  liftIO $ print instructions
  let programNames =
        Set.fromList
          . map execProgramName
          $ (iForallExecs instructions ++ iExistsExecs instructions)
  programs <- sequence $ Map.fromSet (readJavaFile instrFilePath) programNames
  liftIO $ print programs
  return ()
 where
  reportResult (Left  err) = putStrLn $ "Error: " ++ err
  reportResult (Right () ) = return ()

parseArgs :: [String] -> ExceptT String IO FilePath
parseArgs [filePath] = return filePath
parseArgs _          = liftIO showUsage >> throwError "no filename provided"

showUsage :: IO ()
showUsage = do
  progName <- getProgName
  putStrLn ("Usage: " ++ progName ++ " <instructions.jklive>")

readJavaFile :: String -> String -> ExceptT String IO JavaSyntax.CompilationUnit
readJavaFile instrFilePath programName = do
  let filePath = replaceFileName instrFilePath (programName ++ ".java")
  fileContents <- liftIO $ readFile filePath
  liftEither
    $ left ((("could not parse Java file `" ++ filePath ++ "`:\n") ++) . show)
    $ JavaParser.parser JavaParser.compilationUnit fileContents
