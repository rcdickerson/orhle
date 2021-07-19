module Main where

import Orhle
import System.Environment
import System.Exit
import Text.Show.Pretty ( pPrint, pPrintList )

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
     Nothing   -> showUsage
     Just path -> do
       error "Unimplemented"
--       didAsExpected <- readFile path >>= run
--       if didAsExpected then exitSuccess else exitFailure

parseArgs :: [String] -> Maybe FilePath
parseArgs [path] = Just path
parseArgs _      = Nothing

showUsage :: IO ()
showUsage =
  putStrLn "Usage: orhle <filename>"

-- run :: String -> IO Bool
-- run orhle = do
--   putStrLn ""
--   putStrLn "*******************************************"
--   putStrLn "****               ORHLE               ****"
--   putStrLn "****     The Oracular RHLE Verifier    ****"
--   putStrLn "*******************************************"
--   putStrLn ""
--   case parseOrhle orhle of
--     Left err -> do
--       putStrLn $ "Parse error: " ++ err
--       return False
--     Right (execs, impls, specs, triple, expected) -> do
--       printQuery execs impls specs triple
--       result <- Orhle.verify specs impls triple
--       case result of
--         Left failure -> do
--           printFailure failure
--           return $ expected == Orhle.ExpectFailure
--         Right success -> do
--           printSuccess success
--           return $ expected == Orhle.ExpectSuccess

-- printQuery :: [Orhle.Exec] -> FunImplEnv -> AESpecs -> RhleTriple -> IO ()
-- printQuery execs
--            impls
--            (AESpecs aSpecs eSpecs)
--            (RhleTriple pre aProgs eProgs post) = do
--   putStrLn ":: Executions"
--   mapM_ printExec execs
--   putStrLn ""
--   putStrLn $ ":: Universal Programs"
--   pPrintList aProgs
--   putStrLn ""
--   putStrLn $ ":: Existential Programs"
--   pPrintList eProgs
--   putStrLn ""
--   putStrLn $ ":: Universal Specifications"
--   pPrint aSpecs
--   putStrLn ""
--   putStrLn $ ":: Existential Specifications"
--   pPrint eSpecs
--   putStrLn ""
--   putStrLn $ ":: Precondition"
--   pPrint pre
--   putStrLn ""
--   putStrLn $ ":: Postcondition"
--   pPrint post
--   putStrLn ""

printFailure :: Failure -> IO ()
printFailure (Failure message) = do
  putStrLn $ "Failure:\n  " ++ message

printSuccess :: Success -> IO ()
printSuccess _ = do
  putStrLn "Valid."

printExec :: Exec -> IO ()
printExec (ExecForall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printExec (ExecExists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: ExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"
