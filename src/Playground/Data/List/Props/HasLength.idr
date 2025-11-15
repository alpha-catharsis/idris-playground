---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.HasLength

-------------------
-- Has length proof
-------------------

public export
data HasLength : List a -> Nat -> Type where
  ZeroLen : HasLength [] Z
  SuccLen : HasLength xs m -> HasLength (x::xs) (S m)
  
-----------------------------------
-- Has length uninhabited instances
-----------------------------------

export
Uninhabited (HasLength [] (S m)) where
  uninhabited _ impossible

export
Uninhabited (HasLength (x::xs) Z) where
  uninhabited _ impossible

export
{lenContra : Not (HasLength xs m)} -> Uninhabited (HasLength (x::xs) (S m)) where
  uninhabited (SuccLen lenPrf) = lenContra lenPrf

-----------------------
-- Has length injective
-----------------------

export
hasLengthInjective : HasLength xs m -> HasLength xs n -> m = n
hasLengthInjective ZeroLen ZeroLen = Refl
hasLengthInjective (SuccLen lenPrf) (SuccLen lenPrf') = cong S (hasLengthInjective lenPrf lenPrf')

-----------------------
-- Has length decidable
-----------------------

export
decHasLength : (xs : List a) -> (m : Nat) -> Dec (HasLength xs m)
decHasLength [] Z = Yes ZeroLen
decHasLength [] (S m) = No absurd
decHasLength (x::xs) Z = No absurd
decHasLength (x::xs) (S m) = case decHasLength xs m of
  No lenContra => No absurd
  Yes lenPrf => Yes (SuccLen lenPrf)

