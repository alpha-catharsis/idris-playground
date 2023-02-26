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
plusLeftZeroNeutral : (n : Nat) -> plus Z n = n
plusLeftZeroNeutral _ = repeatZeroId S

%hint
public export
plusRightZeroNeutral : (m : Nat) -> plus m Z = m
plusRightZeroNeutral = repeatSuccOnZero

------------
-- plus succ
------------

%hint
public export
plusLeftSucc : (m, n : Nat) -> plus (S m) n = S (plus m n)
plusLeftSucc = repeatUnfoldOutside S

%hint
public export
plusRightSucc : (m, n : Nat) -> plus m (S n) = S (plus m n)
plusRightSucc m n = rewrite sym (repeatOrdInvariant S m n)
                    in repeatUnfoldInside S m n

-------------------
-- plus commutative
-------------------

%hint
public export
plusCommutative : (m, n : Nat) -> plus m n = plus n m
plusCommutative Z      n = rewrite plusRightZeroNeutral n in Refl
plusCommutative (S m') n = plusCommutative m' (S n)

-------------------
-- plus associative
-------------------

%hint
public export
plusAssociative : (m, n, o : Nat) -> plus m (plus n o) = plus (plus m n) o
plusAssociative Z      n o = Refl
plusAssociative (S m') n o = rewrite repeatUnfoldInside S m' (repeat S n o)
                             in rewrite sym (repeatOrdInvariant S n o)
                             in plusAssociative m' (S n) o

----------------
-- plus constant
----------------

%hint
public export
plusLeftConstant : (m, n, c : Nat) -> (prf : m = n) -> plus c m = plus c n
plusLeftConstant _ _ _ Refl = Refl

%hint
public export
plusRightConstant : (m, n, c : Nat) -> (prf : m = n) -> plus m c = plus n c
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
plusRightOneSucc : (m : Nat) -> plus m (S Z) = S m
plusRightOneSucc m = repeatSuccOnZero (S m)

-----------------
-- plus succ succ
-----------------

%hint
public export
plusLeftSuccSucc : (m, n, o : Nat) -> plus m n = o -> plus (S m) n = S o
plusLeftSuccSucc Z      _ _ prf = cong S prf
plusLeftSuccSucc (S m') n o prf = plusLeftSuccSucc m' (S n) o prf

%hint
public export
plusRightSuccSucc : (m, n, o : Nat) -> plus m n = o -> plus m (S n) = S o
plusRightSuccSucc Z      _ _ prf = cong S prf
plusRightSuccSucc (S m') n o prf = plusRightSuccSucc m' (S n) o prf

-----------------
-- plus succ cong
-----------------

%hint
public export
plusLeftSuccCong : (m, n, o, p : Nat) -> plus m n = plus o p ->
                   plus (S m) n = plus (S o) p
plusLeftSuccCong Z      n o p prf = rewrite plusLeftSucc Z n in
                                    rewrite plusLeftSucc o p in
                                    cong S prf
plusLeftSuccCong (S m') n o p prf = plusLeftSuccCong m' (S n) o p prf

%hint
public export
plusRightSuccCong : (m, n, o, p : Nat) -> plus m n = plus o p ->
                    plus m (S n) = plus o (S p)
plusRightSuccCong Z      n o p prf = rewrite plusRightSucc Z n in
                                     rewrite plusRightSucc o p in
                                     cong S prf
plusRightSuccCong (S m') n o p prf = plusLeftSuccCong m' (S n) o p prf

----------------------
-- plus succ injective
----------------------

%hint
public export
plusLeftSuccInjective : (m, n, o, p : Nat) -> plus (S m) n = plus (S o) p ->
                        plus m n = plus o p
plusLeftSuccInjective Z      n o p prf =
  succInjective (rewrite plusLeftSucc Z n in
                 rewrite sym (plusLeftSucc o p) in prf)
plusLeftSuccInjective (S m') n o p prf =
  plusLeftSuccInjective m' (S n) o p prf

%hint
public export
plusRightSuccInjective : (m, n, o, p : Nat) -> plus m (S n) = plus o (S p) ->
                         plus m n = plus o p
plusRightSuccInjective Z      n o p prf =
  succInjective (rewrite plusRightSucc Z n in
                 rewrite sym (plusRightSucc o p) in prf)
plusRightSuccInjective (S m') n o p prf =
  plusRightSuccInjective m' (S n) o p prf

--------------
-- plus cancel
--------------

%hint
public export
plusLeftCancel : (m, n, n' : Nat) -> plus m n = plus m n' -> n = n'
plusLeftCancel Z      _ _  prf = prf
plusLeftCancel (S m') n n' prf  =
  plusLeftCancel m' n n' (plusRightSuccInjective m' n m' n' prf)

%hint
public export
plusRightCancel : (m, n, m' : Nat) -> plus m n = plus m' n -> m = m'
plusRightCancel m n m' prf = plusLeftCancel n m m'
  (rewrite plusCommutative n m in
   rewrite plusCommutative n m' in prf)

------------------
-- plus impossible
------------------

%hint
public export
noPlusLeftSuccZero : (m, n : Nat) -> Not (plus (S m) n = Z)
noPlusLeftSuccZero Z n contra impossible
noPlusLeftSuccZero (S m') n prf = noPlusLeftSuccZero m' (S n) prf

%hint
public export
noPlusRightSuccZero : (m, n : Nat) -> Not (plus m (S n) = Z)
noPlusRightSuccZero m n = rewrite plusCommutative m (S n)
                          in noPlusLeftSuccZero n m

------------
-- plus zero
------------

%hint
public export
zeroPlusLeftZero : (m, n : Nat) -> plus m n = Z -> m = Z
zeroPlusLeftZero Z _ Refl = Refl
zeroPlusLeftZero (S m') n prf = void (noPlusLeftSuccZero m' n prf)

zeroPlusRightZero : (m, n : Nat) -> plus m n = Z -> n = Z
zeroPlusRightZero _ Z      _   = Refl
zeroPlusRightZero m (S n') prf = void (noPlusRightSuccZero m n' prf)

----------------
-- plus Even/Odd
----------------

%hint
public export
plusEvenEvenIsEven : Even m -> Even n -> Even (plus m n)
plusEvenEvenIsEven EvenZ         rprf = rprf
plusEvenEvenIsEven (EvenS lprf') rprf = plusEvenEvenIsEven lprf' (EvenS rprf)

%hint
public export
plusEvenOddIsOdd : Even m -> Odd n -> Odd (plus m n)
plusEvenOddIsOdd EvenZ         rprf = rprf
plusEvenOddIsOdd (EvenS lprf') rprf = plusEvenOddIsOdd lprf' (OddS rprf)

public export
plusOddOddIsEven : Odd m -> Odd n -> Even (plus m n)
plusOddOddIsEven OddO         OddO         = EvenS EvenZ
plusOddOddIsEven OddO         (OddS rprf') = EvenS (plusOddOddIsEven OddO rprf')
plusOddOddIsEven (OddS lprf') rprf         = plusOddOddIsEven lprf' (OddS rprf)

--------------
-- plus LT/LTE
--------------

%hint
public export
plusLeftLT : (m, n : Nat) -> LT m (plus m (S n))
plusLeftLT Z      _ = LTZero
plusLeftLT (S m') n = rewrite plusLeftSucc m' (S n)
                      in LTSucc (plusLeftLT m' n)

%hint
public export
plusRightLT : (m, n : Nat) -> LT n (plus (S m) n)
plusRightLT m n = rewrite plusCommutative (S m) n in plusLeftLT n m

%hint
public export
plusLeftLTE : (m, n : Nat) -> LTE m (plus m n)
plusLeftLTE Z      _ = LTEZero
plusLeftLTE (S m') n = rewrite plusLeftSucc m' n
                       in LTESucc (plusLeftLTE m' n)

%hint
public export
plusRightLTE : (m, n : Nat) -> LTE n (plus m n)
plusRightLTE m n = rewrite plusCommutative m n in plusLeftLTE n m

----------------
-- plus monotone
----------------

%hint
public export
plusLTEMonotoneRight : (m, n, o : Nat) -> LTE n o -> LTE (plus n m) (plus o m)
plusLTEMonotoneRight m Z      o      LTEZero       = plusRightLTE o m
plusLTEMonotoneRight m (S n') (S o') (LTESucc prf) =
  plusLTEMonotoneRight (S m) n' o' prf

%hint
public export
plusLTEMonotoneLeft : (m, n, o : Nat) -> LTE n o -> LTE (plus m n) (plus m o)
plusLTEMonotoneLeft m n o prf = rewrite plusCommutative m n in
                                rewrite plusCommutative m o in
                                plusLTEMonotoneRight m n o prf

%hint
public export
plusMonotone : (m, n, o, p : Nat) -> LTE m n -> LTE o p ->
               LTE (plus m o) (plus n p)
plusMonotone m n o p lprf rprf = transitiveLTE _ _ _
  (plusLTEMonotoneLeft m o p rprf)
  (plusLTEMonotoneRight p m n lprf)
