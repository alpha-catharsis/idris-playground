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

---------------
-- plus neutral
---------------

%hint
public export
plusLeftZeroNeutral : plus Z m = m
plusLeftZeroNeutral = Refl

%hint
public export
plusRightZeroNeutral : (n : Nat) -> plus n Z = n
plusRightZeroNeutral Z      = Refl
plusRightZeroNeutral (S n') = cong S (plusRightZeroNeutral n')

------------
-- plus succ
------------

%hint
public export
plusLeftSucc : plus (S n) m = S (plus n m)
plusLeftSucc = Refl

%hint
public export
plusRightSucc : (n : Nat) -> (0 m : Nat) -> plus n (S m) = S (plus n m)
plusRightSucc Z      _ = Refl
plusRightSucc (S n') m = cong S (plusRightSucc n' m)

-------------------
-- plus commutative
-------------------

%hint
public export
plusCommutative : (n : Nat) -> (0 m : Nat) -> plus n m = plus m n
plusCommutative Z      m = rewrite plusRightZeroNeutral m in Refl
plusCommutative (S n') m = rewrite plusRightSucc m n'
                           in cong S (plusCommutative n' m)

-------------------
-- plus associative
-------------------

%hint
public export
plusAssociative : (n : Nat) -> (0 m : Nat) -> (0 o : Nat) ->
                  plus n (plus m o) = plus (plus n m) o
plusAssociative Z      _ _ = Refl
plusAssociative (S n') m o = cong S (plusAssociative n' m o)

----------------
-- plus Even/Odd
----------------

%hint
public export
plusEvenEvenIsEven : Even n -> Even m -> Even (plus n m)
plusEvenEvenIsEven EvenZ         rprf = rprf
plusEvenEvenIsEven (EvenS lprf') rprf = EvenS (plusEvenEvenIsEven lprf' rprf)

%hint
public export
plusEvenOddIsOdd : Even n -> Odd m -> Odd (plus n m)
plusEvenOddIsOdd EvenZ         rprf = rprf
plusEvenOddIsOdd (EvenS lprf') rprf = OddS (plusEvenOddIsOdd lprf' rprf)

%hint
public export
plusOddOddIsEven : Odd n -> Odd m -> Even (plus n m)
plusOddOddIsEven OddO                OddO                = EvenS EvenZ
plusOddOddIsEven OddO                (OddS rprf')        =
  EvenS (plusOddOddIsEven OddO rprf')
plusOddOddIsEven (OddS lprf')        OddO                =
  EvenS (plusOddOddIsEven lprf' OddO)
plusOddOddIsEven (OddS lprf' {n=n'}) (OddS rprf' {n=m'}) =
  rewrite plusRightSucc n' (S m') in
  rewrite plusRightSucc n' m' in EvenS (EvenS (plusOddOddIsEven lprf' rprf'))

--------------
-- plus LT/LTE
--------------

-- public export
-- plusLeftLTE : (n : Nat) -> (m : Nat) -> LTE n (plus n m)
-- plusLeftLTE Z      _ = LTEZero
-- plusLeftLTE (S n') m = LTESucc (plusLeftLTE n' m)

-- public export
-- plusRightLTE : (n : Nat) -> (m : Nat) -> LTE m (plus n m)
-- plusRightLTE n m = rewrite plusCommutative n m in plusLeftLTE m n

-- public export
-- plusLeftLT : (n : Nat) -> (m : Nat) -> LT n (plus n (S m))
-- plusLeftLT Z      _ = LTZero
-- plusLeftLT (S n') m = LTSucc (plusLeftLT n' m)

-- public export
-- plusRightLT : (n : Nat) -> (m : Nat) -> LT m (plus (S n) m)
-- plusRightLT n m = rewrite plusCommutative n m in
--                   rewrite sym (plusRightSucc m n) in plusLeftLT m n


-- public export
-- plusLeftLT : (n : Nat) -> (m : Nat) -> LT n (plus n (S m))
-- plusLeftLT Z      Z      = LTNext
-- plusLeftLT Z      (S m') = LTSucc (plusLeftLT Z m')
-- plusLeftLT (S n') m      = bothNextLT (plusLeftLT n' m)
