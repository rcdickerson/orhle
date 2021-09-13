{-# LANGUAGE TypeApplications #-}

module Main where

import Orhle ( FunSpecEnv(..)
             , OrhleParseResult(..)
             , RhleTriple(..)
             , SMTString(..)
             , SMTTypeString(..)
             )
import qualified Orhle
import System.Environment
import System.Exit
import Prettyprinter

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
  case Orhle.parseOrhle @Integer orhle of
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

printParseResult :: ( SMTString t
                    , SMTTypeString t
                    , Pretty t )
                 => OrhleParseResult t -> IO ()
printParseResult result = do
  let (RhleTriple pre aprogs eprogs post) = opr_triple result
  let (FunSpecEnv aspecs especs) = opr_specs result
  putStrLn ":: Executions"
  mapM_ printExec (opr_execs result)
  putStrLn ""
  putStrLn $ ":: Universal Programs"
  putStrLn (show $ indent 4 $ vsep $ map (\p -> pretty "--------" <> hardline <> pretty p) aprogs)
  putStrLn ""
  putStrLn $ ":: Existential Programs"
  putStrLn (show $ indent 4 $ vsep $ map (\p -> pretty "--------" <> hardline <> pretty p) eprogs)
  putStrLn ""
--  putStrLn $ ":: Universal Specifications"
--  putStrLn $ show aspecs
--  putStrLn ""
--  putStrLn $ ":: Existential Specifications"
--  putStrLn $ show especs
--  putStrLn ""
  putStrLn $ ":: Precondition"
  putStrLn $ show $ pretty pre
  putStrLn ""
  putStrLn $ ":: Postcondition"
  putStrLn $ show $ pretty post
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
