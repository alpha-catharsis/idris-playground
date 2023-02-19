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
import Playground.Fn.Repeat.Repeat
import Playground.Fn.Repeat.Theorems.Nat
import Playground.Fn.Repeat.Theorems.Repeat

---------------
-- plus neutral
---------------

%hint
public export
plusLeftZeroNeutral : plus Z m = m
plusLeftZeroNeutral = repeatZeroId S

%hint
public export
plusRightZeroNeutral : (n : Nat) -> plus n Z = n
plusRightZeroNeutral = repeatSuccOnZero

------------
-- plus succ
------------

%hint
public export
plusLeftSucc : plus (S n) m = S (plus n m)
plusLeftSucc = repeatUnfoldOutside S n m

%hint
public export
plusRightSucc : plus n (S m) = S (plus n m)
plusRightSucc = rewrite sym (repeatOrdInvariant S n m)
                in repeatUnfoldInside S n m

-------------------
-- plus commutative
-------------------

%hint
public export
plusCommutative : (n : Nat) -> (0 m : Nat) -> plus n m = plus m n
plusCommutative Z      m = rewrite repeatSuccOnZero m in Refl
plusCommutative (S n') m = plusCommutative n' (S m)

-------------------
-- plus associative
-------------------

%hint
public export
plusAssociative : (n : Nat) -> (0 m : Nat) -> (0 o : Nat) ->
                  plus n (plus m o) = plus (plus n m) o
plusAssociative Z      m o = Refl
plusAssociative (S n') m o = rewrite repeatUnfoldInside S n' (repeat S m o)
                             in rewrite sym (repeatOrdInvariant S m o)
                             in plusAssociative n' (S m) o

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
plusLeftLTE : (n : Nat) -> (0 m : Nat) -> LTE n (plus n m)
plusLeftLTE Z      _ = LTEZero
plusLeftLTE (S n') m = rewrite repeatUnfoldOutside S n' m
                       in LTESucc (plusLeftLTE n' m)

%hint
public export
plusRightLTE : (0 n : Nat) -> (m : Nat) -> LTE m (plus n m)
plusRightLTE n m = rewrite plusCommutative n m in plusLeftLTE m n

%hint
public export
plusLeftLT : (n : Nat) -> (0 m : Nat) -> LT n (plus n (S m))
plusLeftLT Z      _ = LTZero
plusLeftLT (S n') m = rewrite repeatUnfoldOutside S n' (S m)
                      in LTSucc (plusLeftLT n' m)

%hint
public export
plusRightLT : (0 n : Nat) -> (m : Nat) -> LT m (plus (S n) m)
plusRightLT n m = rewrite plusCommutative (S n) m in plusLeftLT m n
