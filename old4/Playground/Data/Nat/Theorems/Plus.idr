---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Plus

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
import Playground.Data.Nat.Ops.Plus
import Playground.Data.Nat.Ops.Succ
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd
import Playground.Data.Nat.Rel.LT
import Playground.Data.Nat.Rel.LTE
import Playground.Data.Nat.Theorems.EvenOdd
import Playground.Data.Nat.Theorems.Ord
import Playground.Data.Nat.Theorems.Succ

---------------
-- plus neutral
---------------

-- public export
-- plusLeftZeroNeutral : (n : Nat) -> plus 0 n = n
-- plusLeftZeroNeutral Z      = Refl
-- plusLeftZeroNeutral (S n') = succCong (plusLeftZeroNeutral n')

-- public export
-- plusRightZeroNeutral : (m : Nat) -> plus m 0 = m
-- plusRightZeroNeutral _ = Refl

------------
-- plus succ
------------

-- public export
-- plusLeftSucc : (m, n : Nat) -> plus (succ m) n = succ (plus m n)
-- plusLeftSucc _ Z      = Refl
-- plusLeftSucc m (S n') = succCong (plusLeftSucc m n')

-- public export
-- plusRightSucc : (m, n : Nat) -> plus m (succ n) = succ (plus m n)
-- plusRightSucc _ _ = Refl

-------------------
-- plus commutative
-------------------

-- public export
-- plusCommutative : (m, n : Nat) -> plus m n = plus n m
-- plusCommutative m Z      = rewrite plusLeftZeroNeutral m in Refl
-- plusCommutative m (S n') = rewrite plusCommutative m n' in
--                            rewrite plusLeftSucc n' m in Refl

-------------------
-- plus associative
-------------------

-- public export
-- plusAssociative : (m, n, o : Nat) -> plus m (plus n o) = plus (plus m n) o
-- plusAssociative _ _ Z      = Refl
-- plusAssociative m n (S o') = rewrite plusAssociative m n o' in Refl

-----------------
-- plus succ move
-----------------

-- public export
-- plusMoveSuccRight : (m, n : Nat) -> plus (succ m) n = plus m (succ n)
-- plusMoveSuccRight m n = rewrite plusLeftSucc m n in
--                         rewrite sym (plusRightSucc m n) in Refl

-- public export
-- plusMoveSuccLeft : (m, n : Nat) -> plus m (succ n) = plus (succ m) n
-- plusMoveSuccLeft m n = rewrite plusCommutative (succ m) n in
--                        rewrite plusCommutative m (succ n) in
--                        plusMoveSuccRight n m

------------
-- plus swap
------------

-- public export
-- plusSwapLeft : (m, n, o : Nat) -> plus m (plus n o) = plus n (plus m o)
-- plusSwapLeft m n o = rewrite plusAssociative n m o in
--                      rewrite plusCommutative n m in
--                      rewrite sym (plusAssociative m n o) in Refl

-- public export
-- plusSwapRight : (m, n, o : Nat) -> plus (plus m n) o = plus (plus m o) n
-- plusSwapRight m n o = rewrite sym (plusAssociative m o n) in
--                       rewrite plusCommutative o n in
--                       rewrite plusAssociative m n o in Refl

-- public export
-- plusSwap : (m, n, o, p : Nat) ->
--            plus (plus m n) (plus o p) = plus (plus m o) (plus n p)
-- plusSwap m n o p = rewrite sym (plusAssociative m o (plus n p)) in
--                    rewrite plusSwapLeft o n p in
--                    rewrite plusAssociative m n (plus o p) in Refl

----------------
-- plus constant
----------------

-- public export
-- plusLeftConstant : (c : Nat) -> (prf : m = n) -> plus c m = plus c n
-- plusLeftConstant _ Refl = Refl

-- public export
-- plusRightConstant : (c : Nat) -> (prf : m = n) -> plus m c = plus n c
-- plusRightConstant _ Refl = Refl

-----------
-- plus one
-----------

-- public export
-- plusLeftOneSucc : (n : Nat) -> plus (succ Z) n = S n
-- plusLeftOneSucc Z      = Refl
-- plusLeftOneSucc (S n') = succCong (plusLeftOneSucc n')

-- public export
-- plusRightOneSucc : (m : Nat) -> plus m (succ Z) = S m
-- plusRightOneSucc _ = Refl

-----------------
-- plus succ succ
-----------------

-- public export
-- plusLeftSuccSucc : plus m n = o -> plus (succ m) n = S o
-- plusLeftSuccSucc = rewrite plusLeftSucc m n in succCong

-- public export
-- plusRightSuccSucc : plus m n = o -> plus m (succ n) = S o
-- plusRightSuccSucc = succCong

-----------------
-- plus succ cong
-----------------

-- public export
-- plusLeftSuccCong : plus m n = plus o p -> plus (succ m) n = plus (succ o) p
-- plusLeftSuccCong = rewrite plusLeftSucc m n in
--                    rewrite plusLeftSucc o p in succCong

-- public export
-- plusRightSuccCong : plus m n = plus o p -> plus m (succ n) = plus o (succ p)
-- plusRightSuccCong = succCong

-- public export
-- plusBothSuccCong : plus m n = plus o p ->
--                    plus (succ m) (succ n) = plus (succ o) (succ p)
-- plusBothSuccCong prf = succCong (plusLeftSuccCong prf)

----------------------
-- plus succ injective
----------------------

-- public export
-- plusLeftSuccInjective : plus (succ m) n = plus (succ o) p ->
--                         plus m n = plus o p
-- plusLeftSuccInjective prf = succInjective
--   (rewrite sym (plusLeftSucc m n) in rewrite sym (plusLeftSucc o p) in prf)

-- public export
-- plusRightSuccInjective : plus m (succ n) = plus o (succ p) ->
--                          plus m n = plus o p
-- plusRightSuccInjective = succInjective

-- public export
-- plusBothSuccInjective : plus (succ m) (succ n) = plus (succ o) (succ p) ->
--                         plus m n = plus o p
-- plusBothSuccInjective prf = succInjective (succInjective
--   (rewrite sym (plusLeftSucc m n) in rewrite sym (plusLeftSucc o p) in prf))

--------------
-- plus cancel
--------------

-- public export
-- plusLeftCancel : (m : Nat) -> plus m n = plus m o -> n = o
-- plusLeftCancel Z      prf = rewrite sym (plusLeftZeroNeutral n) in
--                             rewrite sym (plusLeftZeroNeutral o) in prf
-- plusLeftCancel (S m') prf = plusLeftCancel m' (plusLeftSuccInjective prf)

-- public export
-- plusRightCancel : (m : Nat) -> plus m n = plus m o -> n = o
-- plusRightCancel Z      prf = rewrite sym (plusLeftZeroNeutral n) in
--                              rewrite sym (plusLeftZeroNeutral o) in prf
-- plusRightCancel (S m') prf = plusLeftCancel m' (plusLeftSuccInjective prf)

------------------
-- plus impossible
------------------

-- public export
-- noPlusLeftSuccZero : (0 m, n : Nat) -> Not (plus (succ m) n = 0)
-- noPlusLeftSuccZero Z     Z     prf impossible
-- noPlusLeftSuccZero (S _) Z     prf impossible
-- noPlusLeftSuccZero (S _) (S _) prf impossible

-- public export
-- noPlusRightSuccZero : (0 m, n : Nat) -> Not (plus m (succ n) = 0)
-- noPlusRightSuccZero Z     Z     prf impossible
-- noPlusRightSuccZero (S _) Z     prf impossible
-- noPlusRightSuccZero (S _) (S _) prf impossible

------------
-- plus zero
------------

-- public export
-- zeroPlusLeftZero : (m, n : Nat) -> plus m n = 0 -> m = 0
-- zeroPlusLeftZero _ Z      prf = prf
-- zeroPlusLeftZero m (S n') prf = void (noPlusRightSuccZero m n' prf)

-- public export
-- zeroPlusRightZero : (m, n : Nat) -> plus m n = 0 -> n = 0
-- zeroPlusRightZero _ Z      prf = Refl
-- zeroPlusRightZero m (S n') prf = void (noPlusLeftSuccZero m n'
--   (rewrite plusLeftSucc m n' in prf))

----------------
-- plus Even/Odd
----------------

-- public export
-- plusEvenEvenIsEven : Even m -> Even n -> Even (plus m n)
-- plusEvenEvenIsEven lprf EvenZ         = lprf
-- plusEvenEvenIsEven lprf (EvenS rprf') = EvenS (plusEvenEvenIsEven lprf rprf')

-- public export
-- plusEvenOddIsOdd : Even m -> Odd n -> Odd (plus m n)
-- plusEvenOddIsOdd lprf OddO         = succEvenIsOdd lprf
-- plusEvenOddIsOdd lprf (OddS rprf') = OddS (plusEvenOddIsOdd lprf rprf')

-- public export
-- plusOddEvenIsOdd : Odd m -> Even n -> Odd (plus m n)
-- plusOddEvenIsOdd lprf rprf =
--   rewrite plusCommutative m n in plusEvenOddIsOdd rprf lprf

-- public export
-- plusOddOddIsEven : Odd m -> Odd n -> Even (plus m n)
-- plusOddOddIsEven lprf OddO         = succOddIsEven lprf
-- plusOddOddIsEven lprf (OddS rprf') = EvenS (plusOddOddIsEven lprf rprf')

-- public export
-- plusSameIsEven : (m : Nat) -> Even (plus m m)
-- plusSameIsEven Z      = EvenZ
-- plusSameIsEven (S m') = rewrite plusLeftSucc m' m' in EvenS (plusSameIsEven m')

--------------
-- plus LT/LTE
--------------

-- public export
-- plusLeftLT : (m, n : Nat) -> LT m (plus m (succ n))
-- plusLeftLT Z      _     = LTZero
-- plusLeftLT (S m') n     = rewrite plusLeftSucc m' n in LTSucc (plusLeftLT m' n)

-- public export
-- plusRightLT : (m, n : Nat) -> LT n (plus (succ m) n)
-- plusRightLT m n = rewrite plusCommutative (S m) n in plusLeftLT n m

-- public export
-- plusLeftLTE : (m, n : Nat) -> LTE m (plus m n)
-- plusLeftLTE Z      _ = LTEZero
-- plusLeftLTE (S m') n = rewrite plusLeftSucc m' n in LTESucc (plusLeftLTE m' n)

-- public export
-- plusRightLTE : (m, n : Nat) -> LTE n (plus m n)
-- plusRightLTE m n = rewrite plusCommutative m n in plusLeftLTE n m

----------------
-- plus monotone
-- ----------------

-- public export
-- plusLTEMonotoneRight : (m, n, o : Nat) -> LTE n o -> LTE (plus n m) (plus o m)
-- plusLTEMonotoneRight m      Z      o      LTEZero       =
--   rewrite plusLeftZeroNeutral m in plusRightLTE o m
-- plusLTEMonotoneRight Z      (S n') (S o') (LTESucc prf) = LTESucc prf
-- plusLTEMonotoneRight (S m') (S n') (S o') (LTESucc prf) =
--   LTESucc (plusLTEMonotoneRight m' (S n') (S o') (LTESucc prf))


-- public export
-- plusLTEMonotoneLeft : (m, n, o : Nat) -> LTE n o -> LTE (plus m n) (plus m o)
-- plusLTEMonotoneLeft m n o prf = rewrite plusCommutative m n in
--                                 rewrite plusCommutative m o in
--                                 plusLTEMonotoneRight m n o prf

-- public export
-- plusMonotone : (m, n, o, p : Nat) -> LTE m n -> LTE o p ->
--                LTE (plus m o) (plus n p)
-- plusMonotone m n o p lprf rprf = transitiveLTE
--   (plusLTEMonotoneLeft m o p rprf)
--   (plusLTEMonotoneRight p m n lprf)
