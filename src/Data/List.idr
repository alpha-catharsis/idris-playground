---------------------
-- Module declaration
---------------------

module Data.List

------------------
-- List definition
------------------

infixr 7 ::

public export
data List : Type -> Type where
  Nil : List a
  (::) : a -> List a -> List a
