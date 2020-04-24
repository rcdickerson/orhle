module Main where

import KLiveParser
import Orhle
import System.Environment
import System.Exit
import Z3.Monad

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
runKLive klive = do
  putStrLn "*******************************************"
  putStrLn "****               ORHLE               ****"
  putStrLn "**** k-Liveness Hyperproperty Verifier ****"
  putStrLn "*******************************************"
  putStrLn ""
  case parseKLive klive of
    Left  err -> return $ ((show err) ++ "\n", False)
    Right (execs, query, expected) -> do
      putStrLn ":: Executions"
      mapM_ printQExec execs
      putStrLn ""
      (output, success) <- evalZ3 $ runKLQuery query
      let didAsExpected = if success
                            then expected == KLSuccess
                            else expected == KLFailure
      return (output, didAsExpected)

printQExec :: QExec -> IO ()
printQExec (QEForall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printQExec (QEExists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: QExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"

runKLQuery :: Z3 KLQuery -> Z3 (String, Bool)
runKLQuery query = do
  KLQuery specs pre forall exists post <- query
  let trip = RHLETrip pre forall exists post
  (result, trace) <- rhleVerifier specs trip
  traceStr <- ppVTrace trace
  return $ case result of
      Left  reason -> (traceStr ++ "Invalid. " ++ reason, False)
      Right _      -> (traceStr ++ "Valid.", True)
