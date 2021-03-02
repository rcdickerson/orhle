module Orhle.Abduction.AbdTrace
  ( AbdTrace(..)
  , ATWriter
  , logAbdFailure
  , logAbdFlatten
  , logAbdFormula
  , logAbdMessage
  , logAbdStart
  , logAbdSuccess
  , ppAbdTrace
  ) where

import Control.Monad.Writer
import Orhle.Assertion
import qualified Orhle.SMT as SMT

data AbdTrace = ATAbdStart [String] Assertion Assertion
              | ATFailure String
              | ATFlatten String Assertion Assertion
              | ATFormula String Assertion
              | ATMessage String
              | ATSuccess

type ATWriter m a = WriterT [AbdTrace] m a

logAbdFailure :: (Monad m) => String -> ATWriter m ()
logAbdFailure message = do tell [ATFailure message]

logAbdFlatten :: (Monad m) => String -> Assertion -> Assertion -> ATWriter m ()
logAbdFlatten name from to = do tell [ATFlatten name from to]

logAbdFormula :: (Monad m) => String -> Assertion -> ATWriter m ()
logAbdFormula message formula = do tell [ATFormula message formula]

logAbdMessage :: (Monad m) => String -> ATWriter m ()
logAbdMessage message = do tell [ATMessage message]

logAbdStart :: (Monad m) => [String] -> Assertion -> Assertion -> ATWriter m ()
logAbdStart abdDescs pre post = do tell [ATAbdStart abdDescs pre post]

logAbdSuccess :: (Monad m) => ATWriter m ()
logAbdSuccess = do tell [ATSuccess]


ppAbdTrace :: [AbdTrace] -> IO String
ppAbdTrace = ppAbdTrace' 0

ppAbdTrace' :: Int -> [AbdTrace] -> IO String
ppAbdTrace' _ [] = return ""
ppAbdTrace' indent (t:ts) = return ""
  --do
  -- rest <- ppAbdTrace' indent ts
  -- case t of
  --   ATAbdStart abdNames pre post -> do
  --     let preStr  = SMT.exprToString pre
  --     let postStr = SMT.exprToString post
  --     return $ start ++ "!! Starting Abduction\n"
  --                    ++ "Abducibles: " ++ (show abdNames) ++ "\n"
  --                    ++ "Precondition: " ++ preStr ++ "\n"
  --                    ++ "Postcondition: " ++ postStr ++ "\n"
  --                    ++ rest
  --   ATFailure msg -> return $ start ++ "Abduction Failure: " ++ msg ++ "\n" ++ rest
  --   ATFlatten name from to -> do
  --     let fromStr = SMT.exprToString from
  --     let toStr   = SMT.exprToString to
  --     return $ start ++
  --       name ++ " before flatten: " ++ fromStr ++ "\n" ++
  --       name ++ " after flatten: "  ++ toStr   ++ "\n" ++ rest
  --   ATFormula msg formula -> do
  --     let formulaStr = SMT.exprToString formula
  --     return $ start ++ msg ++ ": " ++ formulaStr ++ "\n" ++ rest
  --   ATMessage msg -> return $ start ++ msg ++ "\n" ++ rest
  --   ATSuccess -> return "Success\n"
  -- where start = (concat $ replicate indent " ")
