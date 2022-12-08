---------------------
-- Module declaration
---------------------

module Playground.Data.List.List

-----------------
-- List data type
-----------------

public export
data List : Type -> Type where
  E : List a
  C : a -> List a -> List a
