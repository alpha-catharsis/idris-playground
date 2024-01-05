---------------------
-- Module declaration
---------------------

module Playground.Data.List.List

------------------
-- List definition
------------------

infixr 7 ::

public export
data List : Type -> Type where
  Nil : List a
  (::) : a -> List a -> List a

%name List xs, ys, zs, ws
