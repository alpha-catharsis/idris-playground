---------------------
-- Module declaration
---------------------

module Data.Prod.Prod

---------------------
-- Data types product
---------------------

public export
data Prod : Type -> Type -> Type where
  MkProd : (x : a) -> (y : b) -> Prod a b

----------------------
-- Product projections
----------------------

public export
proj1 : Prod a b -> a
proj1 (MkProd x _) = x

public export
proj2 : Prod a b -> b
proj2 (MkProd _ y) = y
