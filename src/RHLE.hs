module RHLE where

import Conditions
import Hoare
import HoareE
import Imp

data RHLETrip = RHLETrip
  { rhlePre :: Cond
  , rhleProgA :: Prog
  , rhleProgE :: Prog
  , rhlePost :: Cond
  } deriving (Show)

rhleVC :: RHLETrip -> Cond
rhleVC (RHLETrip pre progA progE post) =
  case progA of
    Skip ->
    --------
      case progE of
        Skip        -> CImp pre post
        var := aexp -> hleVC $ HLETrip pre (var := aexp) post
        Seq []      -> CImp pre post
        Seq (s:ss)  ->
            CAnd (hleVC $ HLETrip pre s phi')
                 (rhleVC $ RHLETrip phi' progA (Seq ss) post)
            where phi' = (hleSP pre s)
        If bexp s1 s2 ->
            let c = bexpToCond bexp in
                CAnd (rhleVC $ RHLETrip (CAnd pre c) progA s1 post)
                     (rhleVC $ RHLETrip (CAnd pre (CNot c)) progA s2 post)
        Call (UFunc name params fpre fpost) -> CImp
            (CImp pre (bexpToCond fpre))
            (CImp (CAbducible name params) (bexpToCond fpost))
    --------
    var := aexp -> hlVC $ HLTrip pre (var := aexp) post
    Seq []      -> CImp pre post
    Seq (s:ss)  ->
        CAnd (hlVC $ HLTrip pre s phi')
             (rhleVC $ RHLETrip phi' (Seq ss) progE post)
        where phi' = (hlSP pre s)
    If bexp s1 s2 ->
        let c = bexpToCond bexp in
            CAnd (rhleVC $ RHLETrip (CAnd pre c) s1 progE post)
                 (rhleVC $ RHLETrip (CAnd pre (CNot c)) s2 progE post)
    Call (UFunc name params fpre fpost) ->
        CAnd (CImp pre (bexpToCond fpre))
             (CImp (CAbducible name params) (bexpToCond fpost))
