module Orhle.Triple
  ( HlTriple(..)
  , HleTriple(..)
  , RhleTriple(..)
  , RevProgram(..)
  , RevRhleTriple(..)
  , filterEmptyRev
  , filterEmptyTrip
  , ppRhleTriple
  , ppRevRhleTriple
  , reverseTriple
  , reverseProgram
  ) where

import Data.List ( intercalate )
import Orhle.Assertion
import Orhle.Imp
import Orhle.SMTString ( showSMT )

data HlTriple = HlTriple
  { hlPre  :: Assertion
  , hlProg :: Program
  , hlPost :: Assertion
  } deriving (Show)

data HleTriple = HleTriple
  { hlePre  :: Assertion
  , hleProg :: Program
  , hlePost :: Assertion
  } deriving (Show)

data RhleTriple = RhleTriple
  { rhlePre    :: Assertion
  , rhleAProgs :: [Program]
  , rhleEProgs :: [Program]
  , rhlePost   :: Assertion
  } deriving (Show)

ppRhleTriple :: RhleTriple -> String
ppRhleTriple (RhleTriple pre aprogs eprogs post) =
    "<< " ++ showSMT pre ++ " >>\n" ++
    (intercalate "\n--------\n" $ map ppProg aprogs) ++ "\n" ++
    "~E\n" ++
    (intercalate "\n--------\n" $ map ppProg eprogs) ++ "\n\n" ++
    "<< " ++ showSMT post ++ " >>"

filterEmptyTrip :: RhleTriple -> RhleTriple
filterEmptyTrip (RhleTriple pre aprogs eprogs post) =
  RhleTriple pre (filterEmpty aprogs) (filterEmpty eprogs) post


-- When reasoning backward, it's convenient to store programs in reverse order.
type RevProgram = Program

data RevRhleTriple = RevRhleTriple Assertion [RevProgram] [RevProgram] Assertion
                     deriving Show

ppRevRhleTriple :: RevRhleTriple -> String
ppRevRhleTriple (RevRhleTriple pre aprogs eprogs post) =
    "<< " ++ showSMT pre ++ " >>\n" ++
    (intercalate "\n--------\n" $ map ppProg aprogs) ++ "\n" ++
    "~E\n" ++
    (intercalate "\n--------\n" $ map ppProg eprogs) ++ "\n\n" ++
    "<< " ++ showSMT post ++ " >>"

reverseProgram :: Program -> RevProgram
reverseProgram program = case program of
  SSeq progs       -> (SSeq . reverse) $ map reverseProgram progs
  SWhile c body iv -> SWhile c (reverseProgram body) iv
  _                -> program

reverseTriple :: RhleTriple -> RevRhleTriple
reverseTriple (RhleTriple pre aprogs eprogs post) =
  RevRhleTriple pre (map reverseProgram aprogs) (map reverseProgram eprogs) post

filterEmptyRev :: RevRhleTriple -> RevRhleTriple
filterEmptyRev (RevRhleTriple pre aprogs eprogs post) =
  RevRhleTriple pre (filterEmpty aprogs) (filterEmpty eprogs) post
