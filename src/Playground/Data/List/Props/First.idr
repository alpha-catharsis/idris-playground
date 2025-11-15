---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.First

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Proper

--------------
-- First proof
--------------

public export
data First : a -> List a -> Type where
  IsFirst : First x (x::xs)
  
------------------------------
-- First uninhabited instances
------------------------------

export
Uninhabited (First x []) where
  uninhabited _ impossible

export
{eqContra : Not (x = y)} -> Uninhabited (First x (y::xs)) where
  uninhabited IsFirst = eqContra Refl

------------------
-- First injective
------------------

export
firstInjective : First x xs -> First y xs -> x = y
firstInjective IsFirst IsFirst = Refl

-----------------
-- First function
-----------------

public export
first : (xs : List a) -> Proper xs -> a
first (x::xs) IsProper = x

------------------
-- First decidable
------------------

export
decFirst : DecEq a => (x : a) -> (xs : List a) -> Dec (First x xs)
decFirst x [] = No absurd
decFirst x (y::xs) = case decEq x y of
  No eqContra => No absurd
  Yes eqPrf => Yes (rewrite eqPrf in IsFirst)


