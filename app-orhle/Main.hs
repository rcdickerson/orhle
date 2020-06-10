module Main where

import Orhle
import OrhleAppParser
import System.Environment
import System.Exit
import qualified SMTMonad as S

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
     Nothing   -> showUsage
     Just path -> do
       (output, didAsExpected) <- readFile path >>= runKLive
       putStrLn output
       if didAsExpected then exitSuccess else exitFailure

parseArgs :: [String] -> Maybe FilePath
parseArgs [path] = Just path
parseArgs _      = Nothing

showUsage :: IO ()
showUsage =
  putStrLn "Usage: klive <filename>"

runKLive :: String -> IO (String, Bool)
runKLive orhle = do
  putStrLn "*******************************************"
  putStrLn "****               ORHLE               ****"
  putStrLn "****     The Oracular RHLE Verifier    ****"
  putStrLn "*******************************************"
  putStrLn ""
  case parseOrhleApp orhle of
    Left  err -> return $ ((show err) ++ "\n", False)
    Right (execs, query, expected) -> do
      putStrLn ":: Executions"
      mapM_ printQExec execs
      putStrLn ""
      (output, success) <- runKLQuery query
      let didAsExpected = if success
                            then expected == OASuccess
                            else expected == OAFailure
      return (output, didAsExpected)

printQExec :: OAExec -> IO ()
printQExec (OAForall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printQExec (OAExists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: OAExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"

runKLQuery :: S.SMT OAQuery -> IO (String, Bool)
runKLQuery query = do
  let specs_trip = do
        OAQuery specs pre forall exists post <- query
        return $ (specs, RHLETrip pre forall exists post)
  (result, trace) <- rhleVerifier specs_trip
  let traceStr = ppVTrace trace
  return $ case result of
      Left  reason -> (traceStr ++ "Invalid. " ++ reason, False)
      Right _      -> (traceStr ++ "Valid.", True)
