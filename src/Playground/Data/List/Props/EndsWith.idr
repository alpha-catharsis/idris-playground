---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.EndsWith

-------------------
-- External imports
-------------------

import Decidable.Equality

------------------
-- Ends With proof
------------------

public export
data EndsWith : List a -> List a -> Type where
  EndsSame : EndsWith xs xs
  EndsPrev : EndsWith xs ys -> EndsWith (x::xs) ys
  
----------------------------------
-- Ends With uninhabited instances
----------------------------------

export
Uninhabited (EndsWith [] (y::ys)) where
  uninhabited _ impossible

export
{eqContra : Not (x::xs = ys)} -> {endsContra : Not (EndsWith xs ys)} -> Uninhabited (EndsWith (x::xs) ys) where
  uninhabited EndsSame = eqContra Refl
  uninhabited (EndsPrev endsPrf) = endsContra endsPrf

----------------------
-- Ends With decidable
----------------------

export
decEndsWith : DecEq a => (xs : List a) -> (ys : List a) -> Dec (EndsWith xs ys)
decEndsWith [] [] = Yes EndsSame
decEndsWith [] (y::ys) = No absurd
decEndsWith (x::xs) ys = case decEq (x::xs) ys of
  No eqContra =>  case decEndsWith xs ys of
    No endsContra => No absurd
    Yes endsPrf => Yes (EndsPrev endsPrf)
  Yes eqPrf => Yes (rewrite eqPrf in EndsSame)
