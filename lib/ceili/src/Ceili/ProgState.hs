{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Ceili.ProgState
  ( ProgState
  , pretty
  , prettyProgState
  , prettyProgStates
  ) where

import Ceili.Name
import Data.Map ( Map )
import qualified Data.Map as Map
import Prettyprinter

type ProgState a = Map Name a

instance CollectableNames (ProgState a) where
  namesIn = Map.keysSet

instance MappableNames (ProgState a) where
  mapNames f = Map.mapKeys f

instance FreshableNames (ProgState a) where
  freshen state = do
    let assocs = Map.toList state
    assocs' <- mapM (\(k, v) -> do k' <- freshen k; return (k', v)) assocs
    return $ Map.fromList assocs'

instance Pretty a => Pretty (ProgState a) where
  pretty = prettyProgState

prettyProgState :: Pretty t => ProgState t -> Doc ann
prettyProgState st = group . encloseSep (flatAlt "{ " "{") (flatAlt " }" "}") ", "
                   $ map prettyAssoc (Map.toList st)
  where prettyAssoc (k, v) = pretty k <+> "->" <+> pretty v

prettyProgStates :: Pretty t => [ProgState t] -> Doc ann
prettyProgStates states = list $ map (align . prettyProgState) states
