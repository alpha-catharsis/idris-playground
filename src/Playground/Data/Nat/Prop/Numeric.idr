---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Prop.Numeric

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Data.Void.Void
import Playground.Prop.Decidable

-------------------
-- NonZero property
-------------------

public export
data NonZero : Nat -> Type where
  IsNonZero : (n : Nat) -> NonZero (S n)

notNonZero : NonZero Z -> Void
notNonZero _ impossible

isNonZero : (n : Nat) -> Dec (NonZero n)
isNonZero Z = No notNonZero
isNonZero (S n) = Yes (IsNonZero n)

--------------
-- Eq property
--------------

public export
data Eq : Nat -> Nat -> Type where
  IsEq : Eq n n

public export
cong : (0 f : Nat -> Nat) -> (p : Eq l r) -> Eq (f l) (f r)
cong f IsEq = IsEq

public export
succInj : Eq (S l) (S r) -> Eq l r
succInj IsEq = IsEq

notEqZeroSucc : Eq Z (S r) -> Void
notEqZeroSucc _ impossible

notEqSuccZero : Eq (S l) Z -> Void
notEqSuccZero _ impossible

public export
isEq : (l : Nat) -> (r : Nat) -> Dec (Eq l r)
isEq Z Z = Yes IsEq
isEq Z (S r) = No notEqZeroSucc
isEq (S l) Z = No notEqSuccZero
isEq (S l) (S r) with (isEq l r)
  isEq (S l) (S r) | Yes prf = Yes (cong S prf)
  isEq (S l) (S r) | No contra = No (\prf => contra (succInj prf))

---------------
-- LTE property
---------------

public export
data LTE : Nat -> Nat -> Type where
  IsLTEZero : LTE Z r
  IsLTESucc : LTE l r -> LTE (S l) (S r)

public export
ltePrev : LTE (S l) (S r) -> LTE l r
ltePrev IsLTEZero impossible
ltePrev (IsLTESucc prf) = prf

public export
notLTESuccZero : LTE (S l) Z -> Void
notLTESuccZero _ impossible

public export
isLTE : (l : Nat) -> (r : Nat) -> Dec (LTE l r)
isLTE Z r = Yes IsLTEZero
isLTE (S l) Z = No notLTESuccZero
isLTE (S l) (S r) with (isLTE l r)
  isLTE (S l) (S r) | Yes prf = Yes (IsLTESucc prf)
  isLTE (S l) (S r) | No contra = No (\prf => contra (ltePrev prf))

---------------
-- LT property
---------------

public export
data LT : Nat -> Nat -> Type where
  IsLTZero : LT Z (S r)
  IsLTSucc : LT l r -> LT (S l) (S r)

----------------
-- Even property
----------------

public export
data Even : Nat -> Type where
  IsEvenZero : Even Z
  IsEvenSucc2 : Even n -> Even (S (S n))

---------------
-- Odd property
---------------

public export
data Odd : Nat -> Type where
  IsOddOne : Odd (S Z)
  IsOddSucc2 : Odd n -> Odd (S (S n))
