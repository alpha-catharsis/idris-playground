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
import Playground.Data.Nat.Ops.Plus
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd
import Playground.Data.Nat.Rel.LT
import Playground.Data.Nat.Rel.LTE
import Playground.Data.Nat.Theorems.EvenOdd
import Playground.Data.Nat.Theorems.Ord
import Playground.Data.Nat.Theorems.Succ
import Playground.Fn.Repeat.Repeat
import Playground.Fn.Repeat.Theorems.Nat
import Playground.Fn.Repeat.Theorems.Repeat

---------------
-- plus neutral
---------------

%hint
public export
plusLeftZeroNeutral : (m : Nat) -> plus Z m = m
plusLeftZeroNeutral _ = repeatZeroId S

%hint
public export
plusRightZeroNeutral : (n : Nat) -> plus n Z = n
plusRightZeroNeutral = repeatSuccOnZero

------------
-- plus succ
------------

%hint
public export
plusLeftSucc : (n, m : Nat) -> plus (S n) m = S (plus n m)
plusLeftSucc = repeatUnfoldOutside S

%hint
public export
plusRightSucc : (n, m : Nat) -> plus n (S m) = S (plus n m)
plusRightSucc n m = rewrite sym (repeatOrdInvariant S n m)
                    in repeatUnfoldInside S n m

-------------------
-- plus commutative
-------------------

%hint
public export
plusCommutative : (n, m : Nat) -> plus n m = plus m n
plusCommutative Z      m = rewrite plusRightZeroNeutral m in Refl
plusCommutative (S n') m = plusCommutative n' (S m)

-------------------
-- plus associative
-------------------

%hint
public export
plusAssociative : (n, m, o : Nat) -> plus n (plus m o) = plus (plus n m) o
plusAssociative Z      m o = Refl
plusAssociative (S n') m o = rewrite repeatUnfoldInside S n' (repeat S m o)
                             in rewrite sym (repeatOrdInvariant S m o)
                             in plusAssociative n' (S m) o

----------------
-- plus constant
----------------

%hint
public export
plusLeftConstant : (n, m, c : Nat) -> (prf : n = m) -> plus c n = plus c m
plusLeftConstant _ _ _ Refl = Refl

%hint
public export
plusRightConstant : (n, m, c : Nat) -> (prf : n = m) -> plus n c = plus m c
plusRightConstant _ _ _ Refl = Refl

-----------
-- plus one
-----------

%hint
public export
plusLeftOneSucc : (n : Nat) -> plus (S Z) n = S n
plusLeftOneSucc _ = Refl

%hint
public export
plusRightOneSucc : (n : Nat) -> plus n (S Z) = S n
plusRightOneSucc n = repeatSuccOnZero (S n)

-----------------
-- plus succ succ
-----------------

%hint
public export
plusLeftSuccSucc : (n, m, o : Nat) -> plus n m = o -> plus (S n) m = S o
plusLeftSuccSucc Z      _ _ prf = cong S prf
plusLeftSuccSucc (S n') m o prf = plusLeftSuccSucc n' (S m) o prf

%hint
public export
plusRightSuccSucc : (n, m, o : Nat) -> plus n m = o -> plus n (S m) = S o
plusRightSuccSucc Z      _ _ prf = cong S prf
plusRightSuccSucc (S n') m o prf = plusRightSuccSucc n' (S m) o prf

-----------------
-- plus succ cong
-----------------

%hint
public export
plusLeftSuccCong : (n, m, o, p : Nat) -> plus n m = plus o p ->
                   plus (S n) m = plus (S o) p
plusLeftSuccCong Z      m o p prf = rewrite plusLeftSucc Z m in
                                    rewrite plusLeftSucc o p in
                                    cong S prf
plusLeftSuccCong (S n') m o p prf = plusLeftSuccCong n' (S m) o p prf

%hint
public export
plusRightSuccCong : (n, m, o, p : Nat) -> plus n m = plus o p ->
                    plus n (S m) = plus o (S p)
plusRightSuccCong Z      m o p prf = rewrite plusRightSucc Z m in
                                     rewrite plusRightSucc o p in
                                     cong S prf
plusRightSuccCong (S n') m o p prf = plusLeftSuccCong n' (S m) o p prf

----------------------
-- plus succ injective
----------------------

%hint
public export
plusLeftSuccInjective : (n, m, o, p : Nat) -> plus (S n) m = plus (S o) p ->
                        plus n m = plus o p
plusLeftSuccInjective Z      m o p prf =
  succInjective (rewrite plusLeftSucc Z m in
                 rewrite sym (plusLeftSucc o p) in prf)
plusLeftSuccInjective (S n') m o p prf =
  plusLeftSuccInjective n' (S m) o p prf

%hint
public export
plusRightSuccInjective : (n, m, o, p : Nat) -> plus n (S m) = plus o (S p) ->
                         plus n m = plus o p
plusRightSuccInjective Z      m o p prf =
  succInjective (rewrite plusRightSucc Z m in
                 rewrite sym (plusRightSucc o p) in prf)
plusRightSuccInjective (S n') m o p prf =
  plusRightSuccInjective n' (S m) o p prf

--------------
-- plus cancel
--------------

%hint
public export
plusLeftCancel : (n, m, m' : Nat) -> plus n m = plus n m' -> m = m'
plusLeftCancel Z      _ _  prf = prf
plusLeftCancel (S n') m m' prf  =
  plusLeftCancel n' m m' (plusRightSuccInjective n' m n' m' prf)

%hint
public export
plusRightCancel : (n, m, n' : Nat) -> plus n m = plus n' m -> n = n'
plusRightCancel n m n' prf = plusLeftCancel m n n'
  (rewrite plusCommutative m n in
   rewrite plusCommutative m n' in prf)

------------------
-- plus impossible
------------------

%hint
public export
noPlusLeftSuccZero : (n, m : Nat) -> Not (plus (S n) m = Z)
noPlusLeftSuccZero Z m contra impossible
noPlusLeftSuccZero (S n') m prf = noPlusLeftSuccZero n' (S m) prf

%hint
public export
noPlusRightSuccZero : (n, m : Nat) -> Not (plus n (S m) = Z)
noPlusRightSuccZero n m = rewrite plusCommutative n (S m)
                          in noPlusLeftSuccZero m n

------------
-- plus zero
------------

%hint
public export
zeroPlusLeftZero : (n, m : Nat) -> plus n m = Z -> n = Z
zeroPlusLeftZero Z _ Refl = Refl
zeroPlusLeftZero (S n') m prf = void (noPlusLeftSuccZero n' m prf)

zeroPlusRightZero : (n, m : Nat) -> plus n m = Z -> m = Z
zeroPlusRightZero _ Z      _   = Refl
zeroPlusRightZero n (S m') prf = void (noPlusRightSuccZero n m' prf)

----------------
-- plus Even/Odd
----------------

%hint
public export
plusEvenEvenIsEven : Even n -> Even m -> Even (plus n m)
plusEvenEvenIsEven EvenZ         rprf = rprf
plusEvenEvenIsEven (EvenS lprf') rprf = plusEvenEvenIsEven lprf' (EvenS rprf)

%hint
public export
plusEvenOddIsOdd : Even n -> Odd m -> Odd (plus n m)
plusEvenOddIsOdd EvenZ         rprf = rprf
plusEvenOddIsOdd (EvenS lprf') rprf = plusEvenOddIsOdd lprf' (OddS rprf)

public export
plusOddOddIsEven : Odd n -> Odd m -> Even (plus n m)
plusOddOddIsEven OddO         OddO         = EvenS EvenZ
plusOddOddIsEven OddO         (OddS rprf') = EvenS (plusOddOddIsEven OddO rprf')
plusOddOddIsEven (OddS lprf') rprf         = plusOddOddIsEven lprf' (OddS rprf)

--------------
-- plus LT/LTE
--------------

%hint
public export
plusLeftLT : (n, m : Nat) -> LT n (plus n (S m))
plusLeftLT Z      _ = LTZero
plusLeftLT (S n') m = rewrite plusLeftSucc n' (S m)
                      in LTSucc (plusLeftLT n' m)

%hint
public export
plusRightLT : (n, m : Nat) -> LT m (plus (S n) m)
plusRightLT n m = rewrite plusCommutative (S n) m in plusLeftLT m n

%hint
public export
plusLeftLTE : (n, m : Nat) -> LTE n (plus n m)
plusLeftLTE Z      _ = LTEZero
plusLeftLTE (S n') m = rewrite plusLeftSucc n' m
                       in LTESucc (plusLeftLTE n' m)

%hint
public export
plusRightLTE : (n, m : Nat) -> LTE m (plus n m)
plusRightLTE n m = rewrite plusCommutative n m in plusLeftLTE m n

----------------
-- plus monotone
----------------

%hint
public export
plusLTEMonotoneRight : (n, m, o : Nat) -> LTE m o -> LTE (plus m n) (plus o n)
plusLTEMonotoneRight n Z      o      LTEZero       = plusRightLTE o n
plusLTEMonotoneRight n (S m') (S o') (LTESucc prf) =
  plusLTEMonotoneRight (S n) m' o' prf

%hint
public export
plusLTEMonotoneLeft : (n, m, o : Nat) -> LTE m o -> LTE (plus n m) (plus n o)
plusLTEMonotoneLeft n m o prf = rewrite plusCommutative n m in
                                rewrite plusCommutative n o in
                                plusLTEMonotoneRight n m o prf

plusMonotone : (n, m, o, p : Nat) -> LTE n m -> LTE o p ->
               LTE (plus n o) (plus m p)
plusMonotone n m o p lprf rprf = transitiveLTE _ _ _
  (plusLTEMonotoneLeft n o p rprf)
  (plusLTEMonotoneRight p n m lprf)
