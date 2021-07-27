module Main where

import Orhle ( OrhleParseResult(..), RhleTriple(..), FunSpecEnv(..) )
import qualified Orhle
import System.Environment
import System.Exit
import Text.Show.Pretty ( pPrint, pPrintList )

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
     Nothing   -> showUsage
     Just path -> do
       didAsExpected <- readFile path >>= run
       if didAsExpected then exitSuccess else exitFailure

parseArgs :: [String] -> Maybe FilePath
parseArgs [path] = Just path
parseArgs _      = Nothing

showUsage :: IO ()
showUsage =
  putStrLn "Usage: orhle <filename>"

run :: String -> IO Bool
run orhle = do
  putStrLn ""
  putStrLn "*******************************************"
  putStrLn "****               ORHLE               ****"
  putStrLn "****     The Oracular RHLE Verifier    ****"
  putStrLn "*******************************************"
  putStrLn ""
  case Orhle.parseOrhle orhle of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      return False
    Right parseResult -> do
      printParseResult parseResult
      let env = Orhle.SpecImpEnv (opr_impls parseResult) (opr_specs parseResult)
      result <- Orhle.verify env (opr_triple parseResult)
      case result of
        Left failure -> do
          printFailure failure
          return $ (opr_expected parseResult) == Orhle.ExpectFailure
        Right success -> do
          printSuccess success
          return $ (opr_expected parseResult) == Orhle.ExpectSuccess

printParseResult :: OrhleParseResult -> IO ()
printParseResult result = do
  let (RhleTriple pre aprogs eprogs post) = opr_triple result
  let (FunSpecEnv aspecs especs) = opr_specs result
  putStrLn ":: Executions"
  mapM_ printExec (opr_execs result)
  putStrLn ""
  putStrLn $ ":: Universal Programs"
  pPrintList aprogs
  putStrLn ""
  putStrLn $ ":: Existential Programs"
  pPrintList eprogs
  putStrLn ""
  putStrLn $ ":: Universal Specifications"
  pPrint aspecs
  putStrLn ""
  putStrLn $ ":: Existential Specifications"
  pPrint especs
  putStrLn ""
  putStrLn $ ":: Precondition"
  pPrint pre
  putStrLn ""
  putStrLn $ ":: Postcondition"
  pPrint post
  putStrLn ""

printFailure :: Orhle.Failure -> IO ()
printFailure (Orhle.Failure message) = do
  putStrLn $ "Failure:\n  " ++ message

printSuccess :: Orhle.Success -> IO ()
printSuccess _ = do
  putStrLn "Valid."

printExec :: Orhle.Exec -> IO ()
printExec (Orhle.ExecForall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printExec (Orhle.ExecExists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: Orhle.ExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"
