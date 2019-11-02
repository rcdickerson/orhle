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
     Just path -> readFile path >>= runKLive >>= putStrLn

parseArgs :: [String] -> Maybe FilePath
parseArgs [filepath] = Just filepath
parseArgs _ = Nothing

showUsage :: IO ()
showUsage =
  putStrLn "Usage: klive <filename>"

runKLive :: String -> IO String
runKLive klive = do
  putStrLn "*******************************************"
  putStrLn "****               ORHLE               ****"
  putStrLn "**** k-Liveness Hyperproperty Verifier ****"
  putStrLn "*******************************************"
  putStrLn ""
  case parseKLive klive of
    Left  err -> return $ (show err) ++ "\n"
    Right (execs, query, _) -> do
      putStrLn ":: Executions"
      mapM_ printQExec execs
      putStrLn ""
      result <- evalZ3 $ runKLQuery query
      return result

printQExec :: QExec -> IO ()
printQExec (QEForall name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (forall)"
printQExec (QEExists name eid) = putStrLn $ "  " ++ name ++ (eidStr eid) ++ " (exists)"

eidStr :: QExecId -> String
eidStr Nothing = ""
eidStr (Just eid) = "[" ++ eid ++ "]"

runKLQuery :: Z3 KLQuery -> Z3 String
runKLQuery z3Query = do
  (KLQuery spec pre forall exists post) <- z3Query
  let trip = RHLETrip pre forall exists post
  (result, trace) <- noAbdVerifier spec trip
  traceStr <- ppVTrace trace
  return $ traceStr ++ (resultStr result)
  where
    resultStr r = case r of
      Left  reason -> "Failed: " ++ reason
      Right _      -> "Verified."
