---------------------
-- Module declaration
---------------------

module Data.Exp

-------------------------
-- Exponential definition
-------------------------

public export
Exp : Type -> Type -> Type
Exp b a = a -> b
