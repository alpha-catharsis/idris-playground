---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.StartsWith

-------------------
-- External imports
-------------------

import Decidable.Equality

--------------------
-- Starts With proof
--------------------

public export
data StartsWith : List a -> List a -> Type where
  StartsNil : StartsWith xs []
  StartsNext : StartsWith xs ys -> StartsWith (x::xs) (x::ys)
  
------------------------------------
-- Starts With uninhabited instances
------------------------------------

export
Uninhabited (StartsWith [] (x::ys)) where
  uninhabited _ impossible

export
{contra : Either (Not (x = y)) (Not (StartsWith xs ys))} -> Uninhabited (StartsWith (x::xs) (y::ys)) where
  uninhabited StartsNil impossible
  uninhabited (StartsNext startsPrf) = case contra of 
    Left eqContra => eqContra Refl
    Right startsContra => startsContra startsPrf

------------------------
-- Starts With decidable
------------------------

export
decStartsWith : DecEq a => (xs : List a) -> (ys : List a) -> Dec (StartsWith xs ys)
decStartsWith [] (y::ys) = No absurd
decStartsWith xs [] = Yes StartsNil
decStartsWith (x::xs) (y::ys) = case decEq x y of
  No eqContra => ?a
  Yes eqPrf => rewrite eqPrf in case decStartsWith xs ys of
    No startsContra => No absurd
    Yes startsPrf => Yes (StartsNext startsPrf)
