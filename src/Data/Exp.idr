---------------------
-- Module declaration
---------------------

module Data.Exp

-------------------------
-- Exponential definition
-------------------------

public export
data Exp : Type -> Type -> Type where
  MkExp : (f : a -> b) -> Exp b a
