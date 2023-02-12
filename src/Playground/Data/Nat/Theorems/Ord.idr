---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Ord

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LT
import Playground.Data.Nat.Rel.LTE
import Playground.Data.Nat.Theorems.Succ

--------------------
-- LT basic theorems
--------------------

%hint
public export
bothPrevLT : LT (S n) (S m) -> LT n m
bothPrevLT LTZero       impossible
bothPrevLT (LTSucc prf) = prf

%hint
public export
rightNextLT : LT n m -> LT n (S m)
rightNextLT LTZero = LTZero
rightNextLT (LTSucc prf) = LTSucc (rightNextLT prf)

%hint
public export
leftPrevLT : LT (S n) m -> LT n m
leftPrevLT LTZero       impossible
leftPrevLT (LTSucc prf) = rightNextLT prf

%hint
public export
notBothPrevLT : Not (LT (S n) (S m)) -> Not (LT n m)
notBothPrevLT contra prf = contra (LTSucc prf)

%hint
public export
notBothNextLT : Not (LT n m) -> Not (LT (S n) (S m))
notBothNextLT contra prf = contra (bothPrevLT prf)

%hint
public export
notRightPrevLT : Not (LT n (S m)) -> Not (LT n m)
notRightPrevLT contra prf = contra (rightNextLT prf)

%hint
public export
notLeftNextLT : Not (LT n m) -> Not (LT (S n) m)
notLeftNextLT contra prf = contra (leftPrevLT prf)

------------------------
-- LT uninhabited values
------------------------

%hint
public export
notLTEq : Not (LT n n)
notLTEq LTZero impossible
notLTEq (LTSucc prf) = notLTEq prf

%hint
public export
notLeftSuccRightZeroLT : Not (LT (S n) Z)
notLeftSuccRightZeroLT _ impossible

---------------------
-- LTE basic theorems
---------------------

%hint
public export
bothPrevLTE : LTE (S n) (S m) -> LTE n m
bothPrevLTE LTEZero       impossible
bothPrevLTE (LTESucc prf) = prf

%hint
public export
rightNextLTE : LTE n m -> LTE n (S m)
rightNextLTE LTEZero = LTEZero
rightNextLTE (LTESucc prf) = LTESucc (rightNextLTE prf)

%hint
public export
leftPrevLTE : LTE (S n) m -> LTE n m
leftPrevLTE LTEZero       impossible
leftPrevLTE (LTESucc prf) = rightNextLTE prf

%hint
public export
notBothPrevLTE : Not (LTE (S n) (S m)) -> Not (LTE n m)
notBothPrevLTE contra prf = contra (LTESucc prf)

%hint
public export
notBothNextLTE : Not (LTE n m) -> Not (LTE (S n) (S m))
notBothNextLTE contra prf = contra (bothPrevLTE prf)

%hint
public export
notRightPrevLTE : Not (LTE n (S m)) -> Not (LTE n m)
notRightPrevLTE contra prf = contra (rightNextLTE prf)

%hint
public export
notLeftNextLTE : Not (LTE n m) -> Not (LTE (S n) m)
notLeftNextLTE contra prf = contra (leftPrevLTE prf)

--------------------------
-- LTE uninhabited values
--------------------------

%hint
public export
notLTELeftSucc : Not (LTE (S n) n)
notLTELeftSucc LTEZero       impossible
notLTELeftSucc (LTESucc prf) = notLTELeftSucc prf

%hint
public export
notLeftSuccRightZeroLTE : Not (LTE (S n) Z)
notLeftSuccRightZeroLTE _ impossible

-------------------
-- LT/LTE morphisms
-------------------

%hint
public export
LTtoLTE : LT n m -> LTE n m
LTtoLTE LTZero       = LTEZero
LTtoLTE (LTSucc prf) = LTESucc (LTtoLTE prf)

%hint
public export
LTEtoLTOrEq : (n : Nat) -> (m : Nat) -> LTE n m -> Either (n = m) (LT n m)
LTEtoLTOrEq Z      Z      LTEZero       = Left Refl
LTEtoLTOrEq Z      (S m') LTEZero       = Right LTZero
LTEtoLTOrEq (S n') (S m') (LTESucc prf) = case LTEtoLTOrEq n' m' prf of
  Left eqPrf  => Left (succInjective eqPrf)
  Right ltPrf => Right (LTSucc ltPrf)
