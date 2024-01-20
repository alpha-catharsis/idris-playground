---------------------
-- Module declaration
---------------------

module Data.Sigma.Sigma

-----------------
-- Data types sigma
-----------------

public export
data Sigma : (0 a : Type) -> (0 f : a -> Type) -> Type where
  MkSigma : (x : a) -> (y : f x) -> Sigma a f
