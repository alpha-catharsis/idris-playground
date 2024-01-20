---------------------
-- Module declaration
---------------------

module Data.Sum.Sum

-----------------
-- Data types sum
-----------------

public export
data Sum : Type -> Type -> Type where
  Inj1 : (x : a) -> Sum a b
  Inj2 : (y : b) -> Sum a b
