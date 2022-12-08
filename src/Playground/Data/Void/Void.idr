---------------------
-- Module declaration
---------------------

module Playground.Data.Void.Void

-----------------
-- Void data type
-----------------

public export
data Void : Type where

----------------
-- Not data type
----------------

public export
Not : Type -> Type
Not prop = prop -> Void
