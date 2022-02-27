---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Prop.Numeric

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

-------------------
-- NonZero property
-------------------

public export
data NonZero : (n : Nat) -> Type where
  IsNonZero : (n : Nat) -> NonZero (S n)

--------------
-- Eq property
--------------

public export
data Eq : (l : Nat) -> (r : Nat) -> Type where
  IsEq : (n : Nat) -> Eq n n

---------------
-- LTE property
---------------

public export
data LTE : (l : Nat) -> (r : Nat) -> Type where
  IsLTEZero : LTE Z r
  IsLTESucc : LTE l r -> LTE (S l) (S r)

public export
ltePrev : LTE (S l) (S r) -> LTE l r
ltePrev IsLTEZero impossible
ltePrev (IsLTESucc prf) = prf

---------------
-- LT property
---------------

public export
data LT : (l : Nat) -> (r : Nat) -> Type where
  IsLTZero : LT Z (S r)
  IsLTSucc : LT l r -> LT (S l) (S r)

----------------
-- Even property
----------------

public export
data Even : (n : Nat) -> Type where
  IsEvenZero : Even Z
  IsEvenSucc2 : Even n -> Even (S (S n))

---------------
-- Odd property
---------------

public export
data Odd : (n : Nat) -> Type where
  IsOddOne : Odd (S Z)
  IsOddSucc2 : Odd n -> Odd (S (S n))

