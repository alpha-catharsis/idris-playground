---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.Count

-------------------
-- External imports
-------------------

import Decidable.Equality

--------------
-- Count proof
--------------

public export
data Count : Nat -> a -> List a -> Type where
  CountZero : Count Z x []
  CountSucc : Count m x xs -> Count (S m) x (x::xs)
  CountNext : Count m x xs -> Not (x = y) -> Count m x (y::xs)

------------------------------
-- Count uninhabited instances
------------------------------

export
Uninhabited (Count (S m) x []) where
  uninhabited _ impossible

export
Uninhabited (Count Z x (x::xs)) where
  uninhabited (CountNext cntPrf eqContra) = eqContra Refl

export
{eqContra : Not (x = y)} -> {cntContra : Not (Count m x xs)} -> Uninhabited (Count m x (y::xs)) where
  uninhabited (CountSucc cntPrf) = eqContra Refl
  uninhabited (CountNext cntPrf eqContra') = cntContra cntPrf

export
{cntContra : Not (Count m x xs)} -> Uninhabited (Count (S m) x (x::xs)) where
  uninhabited (CountSucc cntPrf) = cntContra cntPrf
  uninhabited (CountNext cntPrf eqContra) = eqContra Refl

------------------
-- Count injective
------------------

export
countInjective : Count m x xs -> Count n x xs -> m = n
countInjective CountZero CountZero = Refl
countInjective (CountSucc cntPrf) (CountSucc cntPrf') = cong S (countInjective cntPrf cntPrf')
countInjective (CountSucc cntPrf) (CountNext cntPrf' eqContra') = void (eqContra' Refl)
countInjective (CountNext cntPrf eqContra) (CountSucc cntPrf') = void (eqContra Refl)
countInjective (CountNext cntPrf eqContra) (CountNext cntPrf' eqContra') = countInjective cntPrf cntPrf'

-----------------
-- Count function
-----------------

public export
count : DecEq a => a -> List a -> Nat
count x [] = 0
count x (y::xs) = case decEq x y of
  No eqContra => count x xs
  Yes eqPrf => S (count x xs)

------------------
-- Count decidable
------------------

export
decCount : DecEq a => (m : Nat) -> (x : a) -> (xs : List a) -> Dec (Count m x xs)
decCount Z x [] = Yes CountZero
decCount Z x (y::xs) = case decEq x y of
  No eqContra => case decCount Z x xs of
    No cntContra => No absurd
    Yes cntPrf => Yes (CountNext cntPrf eqContra)
  Yes eqPrf => rewrite eqPrf in No absurd
decCount (S m) x [] = No absurd
decCount (S m) x (y::xs) = case decEq x y of
  No eqContra => case decCount (S m) x xs of
    No cntContra => No absurd
    Yes cntPrf => Yes (CountNext cntPrf eqContra)
  Yes eqPrf => rewrite sym eqPrf in case decCount m x xs of
    No cntContra => No absurd
    Yes cntPrf => Yes (CountSucc cntPrf)
