module Main where

import Orhle
import Orhle.OrhleParser
import Orhle.Verifier
import qualified Orhle.SMTMonad as S
import System.Environment
import System.Exit

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
     Nothing   -> showUsage
     Just path -> do
       (output, didAsExpected) <- readFile path >>= run
       putStrLn output
       if didAsExpected then exitSuccess else exitFailure

parseArgs :: [String] -> Maybe FilePath
parseArgs [path] = Just path
parseArgs _      = Nothing

showUsage :: IO ()
showUsage =
  putStrLn "Usage: orhle <filename>"

run :: String -> IO (String, Bool)
run orhle = do
  putStrLn "*******************************************"
  putStrLn "****               ORHLE               ****"
  putStrLn "****     The Oracular RHLE Verifier    ****"
  putStrLn "*******************************************"
  putStrLn ""
  case parseOrhleApp orhle of
    Left  err -> return $ ((show err) ++ "\n", False)
    Right (execs, specs, rhleTriple, expected) -> do
      printQuery execs rhleTriple
      result <- rhleVerifier specs rhleTriple
      let (output, didAsExpected) = case result of
            Left (Failure (S.Model m)) -> ("Invalid. " ++ m, expected == ExpectFailure)
            Right _ -> ("Valid.", expected == ExpectSuccess)
      return (output, didAsExpected)

printQuery :: [Exec] -> RhleTriple -> IO ()
printQuery execs (RhleTriple pre aProgs eProgs post) = do
  putStrLn ":: Executions"
  mapM_ printExec execs
  putStrLn ""
  print "------------------------------------------------\n"
  print $ "Universal Programs:\n" ++ (show aProgs) ++   "\n"
  print "------------------------------------------------\n"
  print $ "Existential Programs:\n" ++ (show eProgs) ++ "\n"
  print "------------------------------------------------\n"

printExec :: Exec -> IO ()
printExec (Forall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printExec (Exists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: ExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"
