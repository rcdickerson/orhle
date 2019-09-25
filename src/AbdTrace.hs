module AbdTrace
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
import Z3.Monad

import Debug.Trace

data AbdTrace = ATAbdStart [String] AST AST
              | ATFailure String
              | ATFlatten String AST AST
              | ATFormula String AST
              | ATMessage String
              | ATSuccess

type ATWriter m a = WriterT [AbdTrace] m a

logAbdFailure :: (Monad m) => String -> ATWriter m ()
logAbdFailure message = do tell [ATFailure message]

logAbdFlatten :: (Monad m) => String -> AST -> AST -> ATWriter m ()
logAbdFlatten name from to = do (trace "<Flatten>") tell [ATFlatten name from to]

logAbdFormula :: (Monad m) => String -> AST -> ATWriter m ()
logAbdFormula message formula = do (trace $ message ++ ": <formula>") tell [ATFormula message formula]

logAbdMessage :: (Monad m) => String -> ATWriter m ()
logAbdMessage message = do (trace message) tell [ATMessage message]

logAbdStart :: (Monad m) => [String] -> AST -> AST -> ATWriter m ()
logAbdStart abdDescs pre post = do tell [ATAbdStart abdDescs pre post]

logAbdSuccess :: (Monad m) => ATWriter m ()
logAbdSuccess = do tell [ATSuccess]


ppAbdTrace :: [AbdTrace] -> Z3 String
ppAbdTrace = ppAbdTrace' 0

ppAbdTrace' :: Int -> [AbdTrace] -> Z3 String
ppAbdTrace' _ [] = return ""
ppAbdTrace' indent (t:ts) = do
  rest <- ppAbdTrace' indent ts
  case t of
    ATAbdStart abdNames pre post -> do
      preStr <- astToString pre
      postStr <- astToString post
      return $ start ++ "!! Starting Abduction\n"
                     ++ "Abducibles: " ++ (show abdNames) ++ "\n"
                     ++ "Precondition: " ++ preStr ++ "\n"
                     ++ "Postcondition: " ++ postStr ++ "\n"
                     ++ rest
    ATFailure msg -> return $ start ++ "Abduction Failure: " ++ msg ++ "\n" ++ rest
    ATFlatten name from to -> do
      fromStr <- astToString from
      toStr   <- astToString to
      return $ start ++
        name ++ " before flatten: " ++ fromStr ++ "\n" ++
        name ++ " after flatten: "  ++ toStr   ++ "\n" ++ rest
    ATFormula msg formula -> do
      formulaStr <- astToString formula
      return $ start ++ msg ++ ": " ++ formulaStr ++ "\n" ++ rest
    ATMessage msg -> return $ start ++ msg ++ "\n" ++ rest
    ATSuccess -> return "Success\n"
  where start = (concat $ replicate indent " ")
