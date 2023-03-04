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
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Succ

----------------------
-- LT basic properties
----------------------

public export
irreflexiveLT : (m : Nat) -> Not (LT m m)
irreflexiveLT Z      LTZero       impossible
irreflexiveLT (S m') (LTSucc prf) = irreflexiveLT m' prf

public export
asymmetricLT : LT m n -> Not (LT n m)
asymmetricLT LTZero        LTZero        impossible
asymmetricLT (LTSucc lprf) (LTSucc rprf) = asymmetricLT lprf rprf

public export
transitiveLT : LT m n -> LT n o -> LT m o
transitiveLT LTZero        (LTSucc _)    = LTZero
transitiveLT (LTSucc lprf) (LTSucc rprf) = LTSucc (transitiveLT lprf rprf)

public export
connectedLT : (m, n : Nat) -> Not (m = n) -> Either (LT m n) (LT n m)
connectedLT Z      Z      contra = void (contra Refl)
connectedLT Z      (S _)  _      = Left LTZero
connectedLT (S _)  Z      _      = Right LTZero
connectedLT (S m') (S n') contra =
  case connectedLT m' n' (noSuccInjective contra) of
    Left lprf  => Left (LTSucc lprf)
    Right rprf => Right (LTSucc rprf)

--------------------
-- LT basic theorems
--------------------

public export
bothPrevLT : LT (succ m) (succ n) -> LT m n
bothPrevLT LTZero       impossible
bothPrevLT (LTSucc prf) = prf

public export
rightNextLT : LT m n -> LT m (succ n)
rightNextLT LTZero = LTZero
rightNextLT (LTSucc prf) = LTSucc (rightNextLT prf)

public export
leftPrevLT : LT (succ m) n -> LT m n
leftPrevLT LTZero       impossible
leftPrevLT (LTSucc prf) = rightNextLT prf

public export
notBothPrevLT : Not (LT (succ m) (succ n)) -> Not (LT m n)
notBothPrevLT contra prf = contra (LTSucc prf)

public export
notBothNextLT : Not (LT m n) -> Not (LT (succ m) (succ n))
notBothNextLT contra prf = contra (bothPrevLT prf)

public export
notRightPrevLT : Not (LT m (succ n)) -> Not (LT m n)
notRightPrevLT contra prf = contra (rightNextLT prf)

public export
notLeftNextLT : Not (LT m n) -> Not (LT (succ m) n)
notLeftNextLT contra prf = contra (leftPrevLT prf)

------------------------
-- LT uninhabited values
------------------------

public export
notLTEq : (0 m : Nat) -> Not (LT m m)
notLTEq _      LTZero       impossible
notLTEq (S m') (LTSucc prf) = notLTEq m' prf

public export
notLeftSuccRightZeroLT : (0 m : Nat) -> Not (LT (succ m) Z)
notLeftSuccRightZeroLT _ _ impossible

-----------------------
-- LTE basic properties
-----------------------

public export
reflexiveLTE : (m : Nat) -> LTE m m
reflexiveLTE Z      = LTEZero
reflexiveLTE (S m') = LTESucc (reflexiveLTE m')

public export
antisymmetricLTE : LTE m n -> LTE n m -> m = n
antisymmetricLTE LTEZero        LTEZero        = Refl
antisymmetricLTE (LTESucc lprf) (LTESucc rprf) =
  succCong (antisymmetricLTE lprf rprf)

public export
transitiveLTE : LTE m n -> LTE n o -> LTE m o
transitiveLTE LTEZero        _              = LTEZero
transitiveLTE (LTESucc lprf) (LTESucc rprf) =
  LTESucc (transitiveLTE lprf rprf)

public export
stronglyConnectedLTE : (m, n : Nat) -> Either (LTE m n) (LTE n m)
stronglyConnectedLTE Z _           = Left LTEZero
stronglyConnectedLTE _ Z           = Right LTEZero
stronglyConnectedLTE (S m') (S n') = case stronglyConnectedLTE m' n' of
  Left lprf  => Left (LTESucc lprf)
  Right rprf => Right (LTESucc rprf)

---------------------
-- LTE basic theorems
---------------------

public export
bothPrevLTE : LTE (succ m) (succ n) -> LTE m n
bothPrevLTE LTEZero       impossible
bothPrevLTE (LTESucc prf) = prf

public export
rightNextLTE : LTE m n -> LTE m (succ n)
rightNextLTE LTEZero = LTEZero
rightNextLTE (LTESucc prf) = LTESucc (rightNextLTE prf)

public export
leftPrevLTE : LTE (succ m) n -> LTE m n
leftPrevLTE LTEZero       impossible
leftPrevLTE (LTESucc prf) = rightNextLTE prf

public export
notBothPrevLTE : Not (LTE (succ m) (succ n)) -> Not (LTE m n)
notBothPrevLTE contra prf = contra (LTESucc prf)

public export
notBothNextLTE : Not (LTE m n) -> Not (LTE (succ m) (succ n))
notBothNextLTE contra prf = contra (bothPrevLTE prf)

public export
notRightPrevLTE : Not (LTE m (succ n)) -> Not (LTE m n)
notRightPrevLTE contra prf = contra (rightNextLTE prf)

public export
notLeftNextLTE : Not (LTE m n) -> Not (LTE (succ m) n)
notLeftNextLTE contra prf = contra (leftPrevLTE prf)

--------------------------
-- LTE uninhabited values
--------------------------

public export
notLTELeftSucc : (0 m : Nat) -> Not (LTE (succ m) m)
notLTELeftSucc _      LTEZero       impossible
notLTELeftSucc (S m') (LTESucc prf) = notLTELeftSucc m' prf

public export
notLeftSuccRightZeroLTE : (0 m : Nat) -> Not (LTE (succ m) Z)
notLeftSuccRightZeroLTE _ _ impossible

-------------------
-- LT/LTE morphisms
-------------------

public export
LTtoLTE : LT m n -> LTE m n
LTtoLTE LTZero       = LTEZero
LTtoLTE (LTSucc prf) = LTESucc (LTtoLTE prf)

public export
LTEtoLTOrEq : (m, n : Nat) -> LTE m n -> Either (m = n) (LT m n)
LTEtoLTOrEq Z      Z      LTEZero       = Left Refl
LTEtoLTOrEq Z      (S m') LTEZero       = Right LTZero
LTEtoLTOrEq (S m') (S n') (LTESucc prf) = case LTEtoLTOrEq m' n' prf of
  Left eqPrf  => Left (succCong eqPrf)
  Right ltPrf => Right (LTSucc ltPrf)
