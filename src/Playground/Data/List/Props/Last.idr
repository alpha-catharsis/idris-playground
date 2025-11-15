---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.Last

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Proper

-------------
-- Last proof
-------------

public export
data Last : a -> List a -> Type where
  LastHere : Last x [x]
  LastThere : Last x xs -> Last x (y::xs)

-----------------------------
-- Last uninhabited instances
-----------------------------

export
Uninhabited (Last x []) where
  uninhabited _ impossible

export
{eqContra : Not (xs = [])} -> {lastContra : Not (Last x xs)} -> Uninhabited (Last x (y::xs)) where
  uninhabited LastHere = eqContra Refl
  uninhabited (LastThere lastPrf) = lastContra lastPrf

export
{eqContra : Not (x = y)} -> Uninhabited (Last x [y]) where
  uninhabited LastHere = eqContra Refl

-----------------
-- Last injective
-----------------

export
lastInjective : Last x xs -> Last y xs -> x = y
lastInjective LastHere LastHere = Refl
lastInjective LastHere (LastThere lastPrf') = void (uninhabited lastPrf')
lastInjective (LastThere lastPrf) LastHere = void (uninhabited lastPrf)
lastInjective (LastThere lastPrf) (LastThere lastPrf') = lastInjective lastPrf lastPrf'

----------------
-- Last function
----------------

public export
last : (xs : List a) -> Proper xs -> a
last [x] IsProper = x
last (x::x'::xs) IsProper = last (x'::xs) IsProper

-----------------
-- Last decidable
-----------------

export
decLast : DecEq a => (x : a) -> (xs : List a) -> Dec (Last x xs)
decLast x [] = No absurd
decLast x (y::xs) = case decLast x xs of
  No lastContra => case decEq xs [] of
    No eqContra => No absurd
    Yes eqPrf => rewrite eqPrf in case decEq x y of
      No eqContra' => No absurd
      Yes eqPrf' => Yes (rewrite eqPrf' in LastHere)
  Yes lastPrf => Yes (LastThere lastPrf)


