---------------------
-- Module declaration
---------------------

module Data.Void

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

--------------------
-- absurd definition
--------------------

public export
absurd : Void -> a
absurd _ impossible
