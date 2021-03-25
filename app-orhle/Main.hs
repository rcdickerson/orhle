module Main where

import Orhle ( AESpecs(..), FunImplEnv(..), RhleTriple(..), parseOrhle )
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
  case parseOrhle orhle of
    Left err -> do
      putStrLn $ "Parse error: " ++ err
      return False
    Right (execs, impls, specs, triple, expected) -> do
      printQuery execs impls specs triple
      result <- Orhle.verify specs impls triple
      case result of
        Left failure -> do
          printFailure failure
          return $ expected == Orhle.ExpectFailure
        Right success -> do
          printSuccess success
          return $ expected == Orhle.ExpectSuccess

printQuery :: [Orhle.Exec] -> FunImplEnv -> AESpecs -> RhleTriple -> IO ()
printQuery execs
           impls
           (AESpecs aSpecs eSpecs)
           (RhleTriple pre aProgs eProgs post) = do
  putStrLn ":: Executions"
  mapM_ printExec execs
  putStrLn ""
  putStrLn $ ":: Universal Programs"
  pPrintList aProgs
  putStrLn ""
  putStrLn $ ":: Existential Programs"
  pPrintList eProgs
  putStrLn ""
  putStrLn $ ":: Universal Specifications"
  pPrint aSpecs
  putStrLn ""
  putStrLn $ ":: Existential Specifications"
  pPrint eSpecs
  putStrLn ""
--  putStrLn ":: Implemented Functions"
--  pPrint impls
--  putStrLn ""
  putStrLn $ ":: Precondition"
  pPrint pre
  putStrLn ""
  putStrLn $ ":: Postcondition"
  pPrint post
  putStrLn ""

printFailure :: Orhle.Failure -> IO ()
printFailure (Orhle.Failure vcs message) = do
--  putStrLn $ "Verification conditions:\n  " ++ (show vcs)
--  putStrLn ""
  putStrLn $ "Failure:\n  " ++ message

printSuccess :: Orhle.Success -> IO ()
printSuccess (Orhle.Success vcs) = do
--  putStrLn $ "Verification conditions:\n  " ++ (show vcs)
--  putStrLn ""
  putStrLn "Valid."

printExec :: Orhle.Exec -> IO ()
printExec (Orhle.ExecForall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printExec (Orhle.ExecExists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: Orhle.ExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"
