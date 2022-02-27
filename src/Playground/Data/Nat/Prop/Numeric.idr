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
import Playground.Prop.Rel

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
  isEq (S l) (S r) | No contra = No (\prf => contra (succInj prf))
  isEq (S l) (S r) | Yes prf = Yes (cong S prf)

public export
reflEq : Refl Eq
reflEq = IsRefl f
  where f : {x : Nat} -> Eq x x
        f = IsEq

public export
symEq : Sym Eq
symEq = IsSym f
  where f : {x : Nat} -> {y : Nat} -> Eq x y -> Eq y x
        f IsEq = IsEq

public export
transEq : Trans Eq
transEq = IsTrans f
  where f : {x : Nat} -> {y : Nat} -> {z : Nat} -> Eq x y -> Eq y z -> Eq x z
        f IsEq IsEq = IsEq

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
  isLTE (S l) (S r) | No contra = No (\prf => contra (ltePrev prf))
  isLTE (S l) (S r) | Yes prf = Yes (IsLTESucc prf)

public export
reflLTE : Refl LTE
reflLTE = IsRefl f
  where f : {x : Nat} -> LTE x x
        f {x=Z} = IsLTEZero
        f {x=S y} = IsLTESucc (f {x=y})

public export
transLTE : Trans LTE
transLTE = IsTrans f
  where f : {x : Nat} -> {y : Nat} -> {z : Nat} -> LTE x y -> LTE y z -> LTE x z
        f IsLTEZero _ = IsLTEZero
        f (IsLTESucc xy) (IsLTESucc yz) = IsLTESucc (f xy yz)

public export
antiSymLTE : AntiSym LTE Eq
antiSymLTE = IsAntiSym f
  where f : {x : Nat} -> {y : Nat} -> LTE x y -> LTE y x -> Eq x y
        f IsLTEZero IsLTEZero = IsEq
        f (IsLTESucc xy) (IsLTESucc yx) = cong S (f xy yx)

---------------
-- LT property
---------------

public export
data LT : Nat -> Nat -> Type where
  IsLTZero : LT Z (S r)
  IsLTSucc : LT l r -> LT (S l) (S r)

public export
ltPrev : LT (S l) (S r) -> LT l r
ltPrev IsLTZero impossible
ltPrev (IsLTSucc prf) = prf

public export
notLTSuccZero : LT (S l) Z -> Void
notLTSuccZero _ impossible

public export
notLTBothZero : LT Z Z -> Void
notLTBothZero _impossible

public export
isLT : (l : Nat) -> (r : Nat) -> Dec (LT l r)
isLT Z Z = No notLTBothZero
isLT Z (S r) = Yes IsLTZero
isLT (S l) Z = No notLTSuccZero
isLT (S l) (S r) with (isLT l r)
  isLT (S l) (S r) | No contra = No (\prf => contra (ltPrev prf))
  isLT (S l) (S r) | Yes prf = Yes (IsLTSucc prf)

----------------
-- Even property
----------------

public export
data Even : Nat -> Type where
  IsEvenZero : Even Z
  IsEvenSucc2 : Even n -> Even (S (S n))

public export
evenPrev : Even (S (S n)) -> Even n
evenPrev IsEvenZero impossible
evenPrev (IsEvenSucc2 prf) = prf

public export
notEvenOne : Even (S Z) -> Void
notEvenOne _ impossible

public export
isEven : (n : Nat) -> Dec (Even n)
isEven Z = Yes IsEvenZero
isEven (S Z) = No notEvenOne
isEven (S (S n)) with (isEven n)
  isEven (S (S n)) | No contra = No (\prf => contra (evenPrev prf))
  isEven (S (S n)) | Yes prf = Yes (IsEvenSucc2 prf)

---------------
-- Odd property
---------------

public export
data Odd : Nat -> Type where
  IsOddOne : Odd (S Z)
  IsOddSucc2 : Odd n -> Odd (S (S n))

public export
oddPrev : Odd (S (S n)) -> Odd n
oddPrev IsOddOne impossible
oddPrev (IsOddSucc2 prf) = prf

public export
notOddZero : Odd Z -> Void
notOddZero _ impossible

public export
isOdd : (n : Nat) -> Dec (Odd n)
isOdd Z = No notOddZero
isOdd (S Z) = Yes IsOddOne
isOdd (S (S n)) with (isOdd n)
  isOdd (S (S n)) | No contra = No (\prf => contra (oddPrev prf))
  isOdd (S (S n)) | Yes prf = Yes (IsOddSucc2 prf)
