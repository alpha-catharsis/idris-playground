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
import Playground.Data.Nat.Theorems.Succ
import Playground.Fun.Repeat.Repeat
import Playground.Fun.Repeat.Theorems.Repeat

---------------
-- Plus neutral
---------------

public export
plusLeftZeroNeutral : (0 n : Nat) -> plus 0 n = n
plusLeftZeroNeutral _ = Refl

public export
plusRightZeroNeutral : (m : Nat) -> plus m 0 = m
plusRightZeroNeutral m = repeatEqNat m

------------
-- Plus succ
------------

public export
plusLeftSucc : (0 m, n : Nat) -> plus (S m) n = S (plus m n)
plusLeftSucc m n = Refl

public export
plusRightSucc : (m : Nat) -> (0 n : Nat) -> plus m (S n) = S (plus m n)
plusRightSucc m n = sym (repeatSuccApp S m n)

-------------------
-- Plus commutative
-------------------

public export
plusCommutative : (m : Nat) -> (0 n : Nat) -> plus m n = plus n m
plusCommutative m n = repeatSwapNat m n

-------------------
-- Plus associative
-------------------

public export
plusAssociative : (m, n, o : Nat) -> plus m (plus n o) = plus (plus m n) o
plusAssociative m n o = rewrite repeatSwapNat n o in
                        rewrite repeatSwap S m o n in
                        repeatSwapNat o (repeat m S n)

-----------------
-- Plus succ move
-----------------

public export
plusMoveSucc : (m : Nat) -> (0 n : Nat) -> plus (S m) n = plus m (S n)
plusMoveSucc m n = repeatSuccApp S m n

------------
-- Plus swap
------------

public export
plusSwapLeft : (m : Nat) -> (0 n, o : Nat) ->
               plus m (plus n o) = plus n (plus m o)
plusSwapLeft m n o = repeatSwap S m n o

public export
plusSwapRight : (m, n, o : Nat) -> plus (plus m n) o = plus (plus m o) n
plusSwapRight m n o = rewrite repeatSwapNat (repeat m S n) o in
                      rewrite repeatSwapNat m n in
                      rewrite repeatSwap S o n m in
                      rewrite repeatSwapNat o m in
                      repeatSwapNat n (repeat m S o)

public export
plusSwap : (m, n, o, p : Nat) ->
           plus (plus m n) (plus o p) = plus (plus m p) (plus o n)
plusSwap m n o p = ?eee

---------------------------------
----------------- TODO: implement
---------------------------------

----------------
-- Plus constant
----------------

public export
plusLeftConstant : (0 c : Nat) -> (0 prf : m = n) -> plus c m = plus c n
plusLeftConstant _ Refl = Refl

public export
plusRightConstant : (0 c : Nat) -> (0 prf : m = n) -> plus m c = plus n c
plusRightConstant _ Refl = Refl

-----------
-- Plus one
-----------

public export
plusLeftOneSucc : (0 n : Nat) -> plus (S Z) n = S n
plusLeftOneSucc _ = Refl

public export
plusRightOneSucc : (m : Nat) -> plus m (S Z) = S m
plusRightOneSucc m = repeatSwapNat m (S Z)

-----------------
-- Plus succ succ
-----------------

public export
plusLeftSuccSucc : plus m n = o -> plus (S m) n = S o
plusLeftSuccSucc Refl = Refl

public export
plusRightSuccSucc : plus m n = o -> plus m (S n) = S o
plusRightSuccSucc Refl = sym (repeatSuccApp S m n)

-----------------
-- Plus succ cong
-----------------

public export
plusLeftSuccCong : (0 prf : plus m n = plus o p) -> plus (S m) n = plus (S o) p
plusLeftSuccCong prf = rewrite prf in Refl

public export
plusRightSuccCong : (0 prf : plus m n = plus o p) -> plus m (S n) = plus o (S p)
plusRightSuccCong prf = rewrite sym (repeatSuccApp S m n) in
                        rewrite sym (repeatSuccApp S o p) in
                        rewrite prf in Refl

public export
plusBothSuccCong : (0 prf : plus m n = plus o p) ->
                   plus (S m) (S n) = plus (S o) (S p)
plusBothSuccCong prf = rewrite sym (repeatSuccApp S m n) in
                       rewrite sym (repeatSuccApp S o p) in
                       rewrite prf in Refl

----------------------
-- Plus succ injective
----------------------

public export
plusLeftSuccInjective : (0 prf : plus (S m) n = plus (S o) p) ->
                        plus m n = plus o p
plusLeftSuccInjective prf = succInjective prf

public export
plusRightSuccInjective : (0 prf : plus m (S n) = plus o (S p)) ->
                        plus m n = plus o p
plusRightSuccInjective prf =
  succInjective (rewrite repeatSuccApp S m n in
                 rewrite repeatSuccApp S o p in prf)

public export
plusBothSuccInjective : (0 prf : plus (S m) (S n) = plus (S o) (S p)) ->
                        plus m n = plus o p
plusBothSuccInjective prf =
  succInjective (succInjective (rewrite repeatSuccApp S m n in
                                rewrite repeatSuccApp S o p in prf))

----------------------
-- Plus succ injective
----------------------

-- public export
-- plusLeftCancel : (m : Nat) -> plus m n = plus m o -> n = o
-- plusLeftCancel m prf = ?dfsdfs
