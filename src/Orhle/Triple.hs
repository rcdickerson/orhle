module Orhle.Triple
  ( HlTriple(..)
  , HleTriple(..)
  , RhleTriple(..)
  , ReverseProgram
  , RevRhleTriple(..)
  , ppRhleTriple
  , ppRevRhleTriple
  , revTriple
  ) where

import Data.List ( intercalate )
import Orhle.Assertion
import Orhle.Imp
import Orhle.ShowSMT ( showSMT )

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



-- When reasoning backward, it's convenient to store programs in reverse order.
type ReverseProgram = Program

data RevRhleTriple = RevRhleTriple Assertion [ReverseProgram] [ReverseProgram] Assertion

ppRevRhleTriple :: RevRhleTriple -> String
ppRevRhleTriple (RevRhleTriple pre aprogs eprogs post) =
    "<< " ++ showSMT pre ++ " >>\n" ++
    (intercalate "\n--------\n" $ map ppProg aprogs) ++ "\n" ++
    "~E\n" ++
    (intercalate "\n--------\n" $ map ppProg eprogs) ++ "\n\n" ++
    "<< " ++ showSMT post ++ " >>"

reverseProgram :: Program -> ReverseProgram
reverseProgram program = case program of
  SSeq progs       -> (SSeq . reverse) $ map reverseProgram progs
  SWhile c body iv -> SWhile c (reverseProgram body) iv
  _                -> program

revTriple :: RhleTriple -> RevRhleTriple
revTriple (RhleTriple pre aprogs eprogs post) =
  RevRhleTriple pre (map reverseProgram aprogs) (map reverseProgram eprogs) post
