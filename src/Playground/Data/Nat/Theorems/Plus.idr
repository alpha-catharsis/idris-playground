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
import Playground.Data.Nat.Props.Even
import Playground.Data.Nat.Props.Odd
import Playground.Data.Nat.Theorems.EvenOdd

---------------
-- plus neutral
---------------

public export
plusLeftZeroNeutral : plus Z m = m
plusLeftZeroNeutral = Refl

public export
plusRightZeroNeutral : (n : Nat) -> plus n Z = n
plusRightZeroNeutral Z      = Refl
plusRightZeroNeutral (S n') = cong S (plusRightZeroNeutral n')

------------
-- plus succ
------------

public export
plusLeftSucc : plus (S n) m = S (plus n m)
plusLeftSucc = Refl

public export
plusRightSucc : (n : Nat) -> (0 m : Nat) -> plus n (S m) = S (plus n m)
plusRightSucc Z      _ = Refl
plusRightSucc (S n') m = cong S (plusRightSucc n' m)

-------------------
-- plus commutative
-------------------

public export
plusCommutative : (n : Nat) -> (0 m : Nat) -> plus n m = plus m n
plusCommutative Z      m = rewrite plusRightZeroNeutral m in Refl
plusCommutative (S n') m = rewrite plusRightSucc m n'
                           in cong S (plusCommutative n' m)

-------------------
-- plus associative
-------------------

public export
plusAssociative : (n : Nat) -> (0 m : Nat) -> (0 o : Nat) ->
                  plus n (plus m o) = plus (plus n m) o
plusAssociative Z      _ _ = Refl
plusAssociative (S n') m o = cong S (plusAssociative n' m o)

----------------
-- plus Even/Odd
----------------

public export
plusEvenEvenIsEven : Even n -> Even m -> Even (plus n m)
plusEvenEvenIsEven EvenZ         rprf = rprf
plusEvenEvenIsEven (EvenS lprf') rprf = EvenS (plusEvenEvenIsEven lprf' rprf)

public export
plusEvenOddIsOdd : Even n -> Odd m -> Odd (plus n m)
plusEvenOddIsOdd EvenZ         rprf = rprf
plusEvenOddIsOdd (EvenS lprf') rprf = OddS (plusEvenOddIsOdd lprf' rprf)

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
