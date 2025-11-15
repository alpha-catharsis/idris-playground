---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.Elem

-------------------
-- External imports
-------------------

import Decidable.Equality

----------------
-- Element proof
----------------

public export
data Elem : a -> List a -> Type where
  Here : Elem x (x::xs)
  There : Elem x xs -> Elem x (y::xs)
  
--------------------------------
-- Element uninhabited instances
--------------------------------

export
Uninhabited (Elem x []) where
  uninhabited _ impossible

export
{eqContra : Not (x = y)} -> {elemContra : Not (Elem x xs)} -> Uninhabited (Elem x (y::xs)) where
  uninhabited Here = eqContra Refl
  uninhabited (There elemPrf) = elemContra elemPrf

--------------------
-- Element decidable
--------------------

export
decElem : DecEq a => (x : a) -> (xs : List a) -> Dec (Elem x xs)
decElem x [] = No absurd
decElem x (y::xs) = case decEq x y of
  No eqContra => case decElem x xs of
    No elemContra => No absurd
    Yes elemPrf => Yes (There elemPrf)
  Yes eqPrf => Yes (rewrite eqPrf in Here)


