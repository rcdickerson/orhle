module Main where

import Orhle
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
                            then expected == OPSuccess
                            else expected == OPFailure
      return (output, didAsExpected)

printQExec :: OPExec -> IO ()
printQExec (OPForall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printQExec (OPExists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: OPExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"

runKLQuery :: S.SMT OPQuery -> IO (String, Bool)
runKLQuery query = do
  let specs_trip = do
        OPQuery specs pre forall exists post <- query
        return $ (specs, RHLETrip pre forall exists post)
  (result, trace) <- rhleVerifier specs_trip
  let traceStr = ppVTrace trace
  return $ case result of
      Left  reason -> (traceStr ++ "Invalid. " ++ reason, False)
      Right _      -> (traceStr ++ "Valid.", True)
