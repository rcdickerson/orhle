module Main where

import Orhle ( RhleTriple(..), parseOrhle )
import qualified Orhle
import System.Environment
import System.Exit
import Text.Show.Pretty ( pPrintList )

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
    Right (execs, specs, rhleTriple, expected) -> do
      printQuery execs rhleTriple
      result <- Orhle.verify specs rhleTriple
      case result of
        Left failure -> do
          printFailure failure
          return $ expected == Orhle.ExpectFailure
        Right success -> do
          printSuccess success
          return $ expected == Orhle.ExpectSuccess

printQuery :: [Orhle.Exec] -> RhleTriple -> IO ()
printQuery execs (RhleTriple pre aProgs eProgs post) = do
  putStrLn ":: Executions"
  mapM_ printExec execs
  putStrLn ""
  putStrLn "------------------------------------------------"
  putStrLn $ "Universal Programs:"
  pPrintList aProgs
  putStrLn "------------------------------------------------"
  putStrLn $ "Existential Programs:"
  pPrintList eProgs
  putStrLn "------------------------------------------------"
  putStrLn $ "Precondition:\n  " ++ (show pre)
  putStrLn "------------------------------------------------"
  putStrLn $ "Postcondition:\n  " ++ (show post)
  putStrLn "------------------------------------------------\n"

printFailure :: Orhle.Failure -> IO ()
printFailure (Orhle.Failure vcs (Orhle.Model model)) = do
  putStrLn $ "Verification conditions:\n  " ++ (show vcs)
  putStrLn ""
  putStrLn $ "Falsifying model:\n  " ++ model
  putStrLn ""
  putStrLn "Invalid."

printSuccess :: Orhle.Success -> IO ()
printSuccess (Orhle.Success vcs) = do
  putStrLn $ "Verification conditions:\n  " ++ (show vcs)
  putStrLn ""
  putStrLn "Valid."

printExec :: Orhle.Exec -> IO ()
printExec (Orhle.Forall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printExec (Orhle.Exists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: Orhle.ExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"
