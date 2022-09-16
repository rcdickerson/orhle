-- Composable program syntax a la "Datatypes a la Carte" by Swierstra.
-- http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Ceili.Language.Compose
  ( (:+:)(..)
  , (:<:)(..)
  ) where

import Prettyprinter

infixr 6 :+:

data (f :+: g) e = Inl (f e) | Inr (g e)
  deriving Functor

instance (Eq (f e), Eq (g e)) => Eq ((f :+: g) e) where
  (Inl f1) == (Inl f2)   =   f1 == f2
  (Inr g1) == (Inr g2)   =   g1 == g2
  _ == _                 =   False

instance (Show (f e), Show (g e)) => Show ((f :+: g) e) where
  show (Inl f) = show f
  show (Inr g) = show g

instance (Pretty (f e), Pretty (g e)) => Pretty ((f :+: g) e) where
  pretty (Inl f) = pretty f
  pretty (Inr g) = pretty g

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a

instance Functor f => f :<: f where
  inj = id

instance {-# OVERLAPPING #-} (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl

instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
