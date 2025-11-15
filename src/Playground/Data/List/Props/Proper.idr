---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.Proper

--------------------
-- Proper list proof
--------------------

public export
data Proper : List a -> Type where
  IsProper : Proper (x::xs)
  
-------------------------------
-- Proper uninhabited instances
-------------------------------

export
Uninhabited (Proper []) where
  uninhabited _ impossible

-------------------
-- Proper decidable
-------------------

export
decProper : (xs : List a) -> Dec (Proper xs)
decProper [] = No absurd
decProper (x::xs) = Yes IsProper
