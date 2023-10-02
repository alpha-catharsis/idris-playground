---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Mult

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Mult
import Playground.Data.Nat.Ops.Plus
import Playground.Data.Nat.Ops.Succ
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd
import Playground.Data.Nat.Rel.LT
import Playground.Data.Nat.Rel.LTE
import Playground.Data.Nat.Theorems.EvenOdd
import Playground.Data.Nat.Theorems.Ord
import Playground.Data.Nat.Theorems.Plus
import Playground.Data.Nat.Theorems.Succ

------------
-- mult zero
------------

-- public export
-- multLeftZeroAbsorb : (m : Nat) -> mult Z m = Z
-- multLeftZeroAbsorb Z      = Refl
-- multLeftZeroAbsorb (S m') = rewrite plusLeftZeroNeutral (mult Z m') in
--                             multLeftZeroAbsorb m'

-- public export
-- multRightZeroAbsorb : (m : Nat) -> mult m Z = Z
-- multRightZeroAbsorb _ = Refl

-----------------
-- mult succ plus
-----------------

-- public export
-- multLeftSuccPlus : (m, n : Nat) -> mult (succ m) n = plus n (mult m n)
-- multLeftSuccPlus m Z      = Refl
-- multLeftSuccPlus m (S n') = rewrite multLeftSuccPlus m n' in
--                             rewrite plusAssociative (S m) n' (mult m n') in
--                             rewrite plusAssociative (S n') m (mult m n') in
--                             rewrite plusLeftSucc m n' in
--                             rewrite plusLeftSucc n' m in
--                             rewrite plusCommutative m n' in Refl

-- public export
-- multRightSuccPlus : (m, n : Nat) -> mult m (succ n) = plus m (mult m n)
-- multRightSuccPlus _ _ = Refl

-------------------
-- mult commutative
-------------------

-- public export
-- multCommutative : (m, n : Nat) -> mult m n = mult n m
-- multCommutative m Z      = sym (multLeftZeroAbsorb m)
-- multCommutative m (S n') = rewrite multLeftSuccPlus n' m in
--                            rewrite multCommutative m n' in Refl

-----------------------
-- mult plus distribute
-----------------------

-- public export
-- multPlusDistribLeft : (m, n, o : Nat) ->
--                       mult (plus m n) o = plus (mult m o) (mult n o)
-- multPlusDistribLeft _ _ Z      = Refl
-- multPlusDistribLeft m n (S o') =
--   rewrite multPlusDistribLeft m n o' in
--   rewrite plusSwap m (mult m o') n (mult n o') in Refl

-- public export
-- multPlusDistribRight : (m, n, o : Nat) ->
--                        mult m (plus n o) = plus (mult m n) (mult m o)
-- multPlusDistribRight _ _ Z      = Refl
-- multPlusDistribRight m n (S o') =
--   rewrite multPlusDistribRight m n o' in plusSwapLeft m (mult m n) (mult m o')

-------------------
-- mult associative
-------------------

-- public export
-- multAssociative : (m, n, o : Nat) -> mult m (mult n o) = mult (mult m n) o
-- multAssociative _ _ Z      = Refl
-- multAssociative m n (S o') = rewrite multPlusDistribRight m n (mult n o') in
--                              rewrite multAssociative m n o' in Refl

---------------
-- mult neutral
---------------

-- public export
-- multLeftOneNeutral : (m : Nat) -> mult (succ Z) m = m
-- multLeftOneNeutral Z      = Refl
-- multLeftOneNeutral (S m') = rewrite plusLeftOneSucc (mult (succ Z) m') in
--                             rewrite multLeftOneNeutral m' in Refl

-- public export
-- multRightOneNeutral : (m : Nat) -> mult m (succ Z) = m
-- multRightOneNeutral _ = Refl


----------------
-- mult two plus
----------------

-- public export
-- multLeftTwoPlus : (m : Nat) -> mult m (succ (succ Z)) = plus m m
-- multLeftTwoPlus _ = Refl

-- public export
-- multRightTwoPlus : (m : Nat) -> mult (succ (succ Z)) m = plus m m
-- multRightTwoPlus m = rewrite multCommutative (succ (succ Z)) m in
--                      multLeftTwoPlus m

------------------------
-- mult zero either zero
------------------------

-- public export
-- multZeroEitherZero : (m, n : Nat) -> mult m n = Z -> Either (m = 0) (n = 0)
-- multZeroEitherZero _ Z      prf = Right Refl
-- multZeroEitherZero m (S n') prf = Left (zeroPlusLeftZero m (mult m n') prf)

----------------
-- mult Even/Odd
----------------

-- public export
-- multRightEvenIsEven : (m, n : Nat) -> Even n -> Even (mult m n)
-- multRightEvenIsEven m Z          EvenZ       = EvenZ
-- multRightEvenIsEven m (S (S n')) (EvenS prf) =
--   rewrite plusAssociative m m (mult m n') in
--   plusEvenEvenIsEven (plusSameIsEven m) (multRightEvenIsEven m n' prf)

-- public export
-- multLeftEvenIsEven : (m, n : Nat) -> Even m -> Even (mult m n)
-- multLeftEvenIsEven m n prf =
--   rewrite multCommutative m n in multRightEvenIsEven n m prf

-- public export
-- multBothOddIsOdd : (m, n : Nat) -> Odd m -> Odd n -> Odd (mult m n)
-- multBothOddIsOdd m (S Z)      mprf _    = mprf
-- multBothOddIsOdd m (S (S n')) mprf nprf =
--   rewrite plusAssociative m m (mult m n') in
--   plusEvenOddIsOdd (plusSameIsEven m)
--                    (multBothOddIsOdd m n' mprf (oddPred n' nprf))

--------------
-- mult LT/LTE
--------------

-- public export
-- multLeftLT : (m, n : Nat) -> LT m (mult (succ m) (succ (succ n)))
-- multLeftLT Z      n =
--   rewrite plusMoveSuccRight Z (plus (S Z) (mult (S Z) n)) in LTZero
-- multLeftLT (S m') n =
--   rewrite plusMoveSuccRight (S m') (plus (S (S m')) (mult (S (S m')) n)) in
--   plusLeftLT (S m') (plus (S (S m')) (mult (S (S m')) n))

-- public export
-- multRightLT : (m, n : Nat) -> LT n (mult (succ (succ m)) (succ n))
-- multRightLT m n = rewrite multCommutative (S (S m)) (S n) in multLeftLT n m

-- public export
-- multLeftLTE : (m, n : Nat) -> LTE m (mult (succ m) (succ n))
-- multLeftLTE Z      n = LTEZero
-- multLeftLTE (S m') n =
--   rewrite plusMoveSuccRight (S m') (mult (S (S m')) n) in
--   plusLeftLTE (S m') (S (mult (S (S m')) n))

-- public export
-- multRightLTE : (m, n : Nat) -> LTE n (mult (succ m) (succ n))
-- multRightLTE m n = rewrite multCommutative (S m) (S n) in multLeftLTE n m

----------------
-- mult monotone
----------------

-- public export
-- multLTEMonotoneLeft : (m, n, o : Nat) -> LTE n o ->
--                      LTE (mult m n) (mult m o)
-- multLTEMonotoneLeft m _ _ LTEZero = LTEZero
-- multLTEMonotoneLeft m (S n') (S o') (LTESucc prf) =
--  plusLTEMonotoneLeft m (mult m n') (mult m o')
--                      (multLTEMonotoneLeft m n' o' prf)

-- public export
-- multLTEMonotoneRight : (m, n, o : Nat) -> LTE n o ->
--                         LTE (mult n m) (mult o m)
-- multLTEMonotoneRight m n o prf = rewrite multCommutative n m in
--                                  rewrite multCommutative o m in
--                                  multLTEMonotoneLeft m n o prf

-- public export
-- multMonotone : (m, n, o, p : Nat) -> LTE m n -> LTE o p ->
--                LTE (mult m o) (mult n p)
-- multMonotone m n o p lprf rprf = transitiveLTE
--   (multLTEMonotoneLeft m o p rprf)
--   (multLTEMonotoneRight p m n lprf)
