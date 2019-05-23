module Abduction
    ( abduce
    ) where

import Conditions
import Imp
import Z3.Monad

abduce :: [Cond] -> [Cond]
abduce conds = conds

data AbductionProblem = SingleAbduction { pre :: Cond
                                        , abd :: String
                                        } deriving (Show)

{-
extractAbducibles :: Cond -> ([AbductionProblem], Cond)
extractAbducibles cond =
  case cond of
    CTrue -> ([], CTrue)
    CFalse -> ([], CFalse)
    e@(CEq _ _) -> ([], e)
    CNot c -> (abducibles, CNot c')
              where (abducibles, c') = extractAbducibles c
    CAnd l r -> (aleft ++ aright, CAnd l' r')
              where (aleft, l') = extractAbducibles l
                    (aright, r') = extractAbducibles r
    COr l r -> (aleft ++ aright, COr l' r')
                  where (aleft, l') = extractAbducibles l
                        (aright, r') = extractAbducibles r
    CImp p q -> (ap ++ aq, CImp p' q')
                where (ap, p') = extractAbducibles p
                      (aq, q') = extractAbducibles q
    CAssignPost var aexp cond -> (abducibles, CAssignPost var aexp cond')
                 where (abducibles, cond') = extractAbducibles cond
    CAbducible pre (UFunc fName fParams fPre fPost) ->
      ([SingleAbduction (CImp (CImp pre $ bexpToCond fPre) $ bexpToCond fPost) fName], CTrue)
-}
