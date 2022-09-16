{-# LANGUAGE TypeApplications #-}

module Ceili.CeiliEnv
  ( Ceili
  , Counterexample(..)
  , Env(..)
  , LogLevel(..)
  , SMT.SatCheckable
  , SMT.ValidCheckable
  , checkSat
  , checkSatB
  , checkSatWithLog
  , checkValid
  , checkValidB
  , checkValidE
  , checkValidWithLog
  , defaultEnv
  , emptyEnv
  , envFreshen
  , envGetNextIds
  , envPutNextIds
  , findCounterexample
  , log_d
  , log_e
  , log_i
  , log_s
  , mkEnv
  , mkSolver
  , remakeSolver
  , runCeili
  , throwError
  ) where

import Ceili.Assertion ( Assertion(..), AssertionParseable, parseAssertion )
import Ceili.Name
import qualified Ceili.SMT as SMT
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Except ( ExceptT, runExceptT, throwError )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified SimpleSMT as SSMT
import System.Log.FastLogger

data Env = Env { env_logger_smt   :: LogType
               , env_logger_debug :: LogType
               , env_logger_error :: LogType
               , env_logger_info  :: LogType
               , env_nextFreshIds :: NextFreshIds
               , env_smtTimeoutMs :: Integer
               , env_smtSolver    :: SSMT.Solver
               }

data LogLevel = LogLevelSMT
              | LogLevelDebug
              | LogLevelInfo
              | LogLevelError
              | LogLevelNone

type Ceili = StateT Env (ExceptT String IO)

runCeili :: Env -> Ceili a -> IO (Either String a)
runCeili env task = runExceptT (evalStateT task env)

mkEnv :: SSMT.Solver -> LogLevel -> Integer -> Set Name -> Env
mkEnv solver minLogLevel smtTimeoutMs names =
  Env { env_logger_smt   = mkSmtLogType minLogLevel
      , env_logger_debug = mkDebugLogType minLogLevel
      , env_logger_info  = mkInfoLogType minLogLevel
      , env_logger_error = mkErrorLogType minLogLevel
      , env_nextFreshIds = buildFreshIds names
      , env_smtTimeoutMs = smtTimeoutMs
      , env_smtSolver    = solver
      }

mkSolver :: IO SSMT.Solver
mkSolver = do
  -- logger <- SSMT.newLogger 0
  solver <- SSMT.newSolver "z3" ["-in", "-t:5000"] $ Nothing
  pure solver

remakeSolver :: Ceili ()
remakeSolver = do
  Env lsmt ldebug linfo lerror fresh timeout oldSolver <- get
  _ <- lift . lift $ SSMT.stop oldSolver
  newSolver <- lift . lift $ mkSolver
  put $ Env lsmt ldebug linfo lerror fresh timeout newSolver

defaultEnv :: SSMT.Solver -> Set Name -> Env
defaultEnv solver = mkEnv solver LogLevelInfo 2000

emptyEnv :: IO Env
emptyEnv = do
  solver <- mkSolver
  pure $ defaultEnv solver Set.empty

mkSmtLogType :: LogLevel -> LogType
mkSmtLogType minLevel = case minLevel of
  LogLevelSMT -> LogStdout defaultBufSize
  _ -> LogNone

mkDebugLogType :: LogLevel -> LogType
mkDebugLogType minLevel = case minLevel of
  LogLevelSMT   -> LogStdout defaultBufSize
  LogLevelDebug -> LogStdout defaultBufSize
  _ -> LogNone

mkInfoLogType :: LogLevel -> LogType
mkInfoLogType minLevel = case minLevel of
  LogLevelSMT   -> LogStdout defaultBufSize
  LogLevelDebug -> LogStdout defaultBufSize
  LogLevelInfo  -> LogStdout defaultBufSize
  _ -> LogNone

mkErrorLogType :: LogLevel -> LogType
mkErrorLogType minLevel = case minLevel of
  LogLevelSMT   -> LogStdout defaultBufSize
  LogLevelDebug -> LogStderr defaultBufSize
  LogLevelInfo  -> LogStderr defaultBufSize
  LogLevelError -> LogStderr defaultBufSize
  _ -> LogNone

getSolver :: Ceili SSMT.Solver
getSolver = get >>= pure . env_smtSolver

logAt :: ToLogStr m => (Env -> LogType) -> m -> Ceili ()
logAt logger message = do
  let messageLS = (toLogStr message) <> toLogStr "\n"
  logType <- get >>= return . logger
  liftIO $ withFastLogger logType ($ messageLS)

log_s :: ToLogStr m => m -> Ceili ()
log_s = logAt env_logger_smt

log_d :: ToLogStr m => m -> Ceili ()
log_d = logAt env_logger_debug

log_i :: ToLogStr m => m -> Ceili ()
log_i = logAt env_logger_info

log_e :: ToLogStr m => m -> Ceili ()
log_e = logAt env_logger_error

logTypeAt :: LogLevel -> Ceili LogType
logTypeAt level = case level of
  LogLevelNone  -> return LogNone
  LogLevelSMT   -> get >>= return . env_logger_smt
  LogLevelDebug -> get >>= return . env_logger_debug
  LogLevelError -> get >>= return . env_logger_error
  LogLevelInfo  -> get >>= return . env_logger_info

checkValid :: SMT.ValidCheckable t => Assertion t -> Ceili SMT.ValidResult
checkValid = checkValidWithLog LogLevelSMT

checkValidB :: SMT.ValidCheckable t => Assertion t -> Ceili Bool
checkValidB assertion = do
  valid <- checkValid assertion
  case valid of
    SMT.Valid        -> pure True
    SMT.Invalid _    -> pure False
    SMT.ValidUnknown -> error "UNK"
    SMT.ValidTimeout -> error "Timeout"

checkValidE :: SMT.ValidCheckable t => Assertion t -> Ceili (Either String Bool)
checkValidE assertion = do
  valid <- checkValid assertion
  pure $ case valid of
    SMT.Valid        -> Right True
    SMT.Invalid _    -> Right False
    SMT.ValidUnknown -> Left "UNK"
    SMT.ValidTimeout -> Left "Timeout"

checkValidWithLog :: SMT.ValidCheckable t
                  => LogLevel
                  -> Assertion t
                  -> Ceili SMT.ValidResult
checkValidWithLog level assertion = do
  solver <- getSolver
  lift . lift $ SMT.checkValidFL solver assertion

checkSat :: SMT.SatCheckable t
         => Assertion t
         -> Ceili SMT.SatResult
checkSat = checkSatWithLog LogLevelSMT

checkSatB :: SMT.SatCheckable t
          => Assertion t
          -> Ceili Bool
checkSatB assertion = do
  sat <- checkSat assertion
  case sat of
    SMT.Sat _      -> return True
    SMT.Unsat      -> return False
    SMT.SatUnknown -> return False
    SMT.SatTimeout -> return False

checkSatWithLog :: SMT.SatCheckable t
                => LogLevel
                -> Assertion t
                -> Ceili SMT.SatResult
checkSatWithLog level assertion = do
  solver <- getSolver
  lift . lift $ SMT.checkSatFL solver assertion

runWithLog :: LogLevel -> (FastLogger -> IO a) -> Ceili a
runWithLog level task = do
  logType <- logTypeAt level
  lift . lift $ withFastLogger logType $ \logger -> task logger

data Counterexample t = Counterexample (Assertion t)
                      | FormulaValid
                      | SMTTimeout
                      | SMTUnknown
                      deriving (Eq, Ord, Show)

findCounterexample :: (SMT.ValidCheckable t, AssertionParseable t)
                   => Assertion t
                   -> Ceili (Counterexample t)
findCounterexample assertion = do
  solver <- getSolver
  result  <- lift . lift $ SMT.checkValidFL solver assertion
  case result of
    SMT.Valid           -> pure FormulaValid
    SMT.ValidUnknown    -> pure SMTUnknown
    SMT.ValidTimeout    -> pure SMTTimeout
    (SMT.Invalid model) -> case parseAssertion model of
                              Left err  -> throwError $ "Error parsing "
                                           ++ show model
                                           ++ ":\n"
                                           ++ show err
                              Right cex -> pure $ Counterexample cex

envGetNextIds :: Ceili NextFreshIds
envGetNextIds = get >>= pure . env_nextFreshIds

envPutNextIds :: NextFreshIds -> Ceili ()
envPutNextIds nextIds = do
  Env logs logd loge logi _ smtTimeout solver <- get
  put $ Env logs logd loge logi nextIds smtTimeout solver

envFreshen :: FreshableNames a => a -> Ceili a
envFreshen a = do
  Env logs logd loge logi nextIds smtTimeout solver <- get
  let (nextIds', a') = runFreshen nextIds a
  put $ Env logs logd loge logi nextIds' smtTimeout solver
  return a'
