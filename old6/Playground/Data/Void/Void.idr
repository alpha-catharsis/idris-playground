---------------------
-- Module declaration
---------------------

module Playground.Data.Void.Void

------------------
-- Void definition
------------------

public export
data Void : Type where

-----------------
-- Not definition
-----------------

public export
Not : Type -> Type
Not a = a -> Void
