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

----------------------
-- LT basic properties
----------------------

%hint
public export
irreflexiveLT : (m : Nat) -> Not (LT m m)
irreflexiveLT Z      LTZero       impossible
irreflexiveLT (S m') (LTSucc prf) = irreflexiveLT m' prf

%hint
public export
asymmetricLT : (m, n : Nat) -> LT m n -> Not (LT n m)
asymmetricLT _      _      LTZero       LTZero         impossible
asymmetricLT (S m') (S n') (LTSucc lprf) (LTSucc rprf) =
  asymmetricLT m' n' lprf rprf

%hint
public export
transitiveLT : (m, n, o : Nat) -> LT m n -> LT n o -> LT m o
transitiveLT _      _      _      LTZero        (LTSucc _)    = LTZero
transitiveLT (S m') (S n') (S o') (LTSucc lprf) (LTSucc rprf) =
  LTSucc (transitiveLT m' n' o' lprf rprf)

%hint
public export
connectedLT : (m, n : Nat) -> Not (m = n) -> Either (LT m n) (LT n m)
connectedLT Z      Z      contra = void (contra Refl)
connectedLT Z      (S n') _      = Left LTZero
connectedLT (S m') Z      _      = Right LTZero
connectedLT (S m') (S n') contra =
  case connectedLT m' n' (noSuccInjective contra) of
    Left lprf  => Left (LTSucc lprf)
    Right rprf => Right (LTSucc rprf)

--------------------
-- LT basic theorems
--------------------

%hint
public export
bothPrevLT : LT (S m) (S n) -> LT m n
bothPrevLT LTZero       impossible
bothPrevLT (LTSucc prf) = prf

%hint
public export
rightNextLT : LT m n -> LT m (S n)
rightNextLT LTZero = LTZero
rightNextLT (LTSucc prf) = LTSucc (rightNextLT prf)

%hint
public export
leftPrevLT : LT (S m) n -> LT m n
leftPrevLT LTZero       impossible
leftPrevLT (LTSucc prf) = rightNextLT prf

%hint
public export
notBothPrevLT : Not (LT (S m) (S n)) -> Not (LT m n)
notBothPrevLT contra prf = contra (LTSucc prf)

%hint
public export
notBothNextLT : Not (LT m n) -> Not (LT (S m) (S n))
notBothNextLT contra prf = contra (bothPrevLT prf)

%hint
public export
notRightPrevLT : Not (LT m (S n)) -> Not (LT m n)
notRightPrevLT contra prf = contra (rightNextLT prf)

%hint
public export
notLeftNextLT : Not (LT m n) -> Not (LT (S m) n)
notLeftNextLT contra prf = contra (leftPrevLT prf)

------------------------
-- LT uninhabited values
------------------------

%hint
public export
notLTEq : Not (LT m m)
notLTEq LTZero impossible
notLTEq (LTSucc prf) = notLTEq prf

%hint
public export
notLeftSuccRightZeroLT : Not (LT (S m) Z)
notLeftSuccRightZeroLT _ impossible

-----------------------
-- LTE basic properties
-----------------------

%hint
public export
reflexiveLTE : (m : Nat) -> LTE m m
reflexiveLTE Z      = LTEZero
reflexiveLTE (S m') = LTESucc (reflexiveLTE m')

%hint
public export
antisymmetricLTE : (m, n : Nat) -> LTE m n -> LTE n m -> m = n
antisymmetricLTE _      _      LTEZero        LTEZero        = Refl
antisymmetricLTE (S m') (S n') (LTESucc lprf) (LTESucc rprf) =
  succCong (antisymmetricLTE m' n' lprf rprf)

%hint
public export
transitiveLTE : (m, n, o : Nat) -> LTE m n -> LTE n o -> LTE m o
transitiveLTE _      _      _      LTEZero        _              = LTEZero
transitiveLTE (S m') (S n') (S o') (LTESucc lprf) (LTESucc rprf) =
  LTESucc (transitiveLTE m' n' o' lprf rprf)

%hint
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

%hint
public export
bothPrevLTE : LTE (S m) (S n) -> LTE m n
bothPrevLTE LTEZero       impossible
bothPrevLTE (LTESucc prf) = prf

%hint
public export
rightNextLTE : LTE m n -> LTE m (S n)
rightNextLTE LTEZero = LTEZero
rightNextLTE (LTESucc prf) = LTESucc (rightNextLTE prf)

%hint
public export
leftPrevLTE : LTE (S m) n -> LTE m n
leftPrevLTE LTEZero       impossible
leftPrevLTE (LTESucc prf) = rightNextLTE prf

%hint
public export
notBothPrevLTE : Not (LTE (S m) (S n)) -> Not (LTE m n)
notBothPrevLTE contra prf = contra (LTESucc prf)

%hint
public export
notBothNextLTE : Not (LTE m n) -> Not (LTE (S m) (S n))
notBothNextLTE contra prf = contra (bothPrevLTE prf)

%hint
public export
notRightPrevLTE : Not (LTE m (S n)) -> Not (LTE m n)
notRightPrevLTE contra prf = contra (rightNextLTE prf)

%hint
public export
notLeftNextLTE : Not (LTE m n) -> Not (LTE (S m) n)
notLeftNextLTE contra prf = contra (leftPrevLTE prf)

--------------------------
-- LTE uninhabited values
--------------------------

%hint
public export
notLTELeftSucc : Not (LTE (S m) m)
notLTELeftSucc LTEZero       impossible
notLTELeftSucc (LTESucc prf) = notLTELeftSucc prf

%hint
public export
notLeftSuccRightZeroLTE : Not (LTE (S m) Z)
notLeftSuccRightZeroLTE _ impossible

-------------------
-- LT/LTE morphisms
-------------------

%hint
public export
LTtoLTE : LT m n -> LTE m n
LTtoLTE LTZero       = LTEZero
LTtoLTE (LTSucc prf) = LTESucc (LTtoLTE prf)

%hint
public export
LTEtoLTOrEq : (m, n : Nat) -> LTE m n -> Either (m = n) (LT m n)
LTEtoLTOrEq Z      Z      LTEZero       = Left Refl
LTEtoLTOrEq Z      (S m') LTEZero       = Right LTZero
LTEtoLTOrEq (S m') (S n') (LTESucc prf) = case LTEtoLTOrEq m' n' prf of
  Left eqPrf  => Left (cong S eqPrf)
  Right ltPrf => Right (LTSucc ltPrf)
