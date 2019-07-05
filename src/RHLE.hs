module RHLE
  ( mkRHLETripFromASTs
  , rhlePreAST
  , rhlePostAST
  , RHLETrip(..)
  ) where

import Imp
import Z3.Monad
import Z3Util

data RHLETrip = RHLETrip
  { rhlePre   :: SMTString
  , rhleProgA :: Prog
  , rhleProgE :: Prog
  , rhlePost  :: SMTString
  } deriving (Show)

rhlePreAST :: RHLETrip -> Z3 AST
rhlePreAST trip = parseSMTLib2String (rhlePre trip) [] [] [] []

rhlePostAST :: RHLETrip -> Z3 AST
rhlePostAST trip = parseSMTLib2String (rhlePost trip) [] [] [] []

mkRHLETripFromASTs :: AST -> Prog -> Prog -> AST -> Z3 RHLETrip
mkRHLETripFromASTs pre progA progE post = do
  preString  <- astToString pre
  postString <- astToString post
  return $ RHLETrip preString progA progE postString
