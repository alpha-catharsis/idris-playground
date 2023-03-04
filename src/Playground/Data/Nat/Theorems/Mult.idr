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
import Playground.Data.Nat.Theorems.Plus
import Playground.Data.Nat.Theorems.Succ

------------
-- mult zero
------------

public export
multLeftZeroAbsorb : (m : Nat) -> mult Z m = Z
multLeftZeroAbsorb Z      = Refl
multLeftZeroAbsorb (S m') = rewrite plusLeftZeroNeutral (mult Z m') in
                            multLeftZeroAbsorb m'

public export
multRightZeroAbsorb : (m : Nat) -> mult m Z = Z
multRightZeroAbsorb _ = Refl

-----------------
-- mult succ plus
-----------------

public export
multLeftSuccPlus : (m, n : Nat) -> mult (succ m) n = plus n (mult m n)
multLeftSuccPlus m Z      = Refl
multLeftSuccPlus m (S n') = rewrite multLeftSuccPlus m n' in
                            rewrite plusAssociative (S m) n' (mult m n') in
                            rewrite plusAssociative (S n') m (mult m n') in
                            rewrite plusLeftSucc m n' in
                            rewrite plusLeftSucc n' m in
                            rewrite plusCommutative m n' in Refl

public export
multRightSuccPlus : (m, n : Nat) -> mult m (succ n) = plus m (mult m n)
multRightSuccPlus _ _ = Refl

-------------------
-- mult commutative
-------------------

public export
multCommutative : (m, n : Nat) -> mult m n = mult n m
multCommutative m Z      = sym (multLeftZeroAbsorb m)
multCommutative m (S n') = rewrite multLeftSuccPlus n' m in
                           rewrite multCommutative m n' in Refl

-----------------------
-- mult plus distribute
-----------------------

public export
multPlusDistribLeft : (m, n, o : Nat) ->
                      mult (plus m n) o = plus (mult m o) (mult n o)
multPlusDistribLeft _ _ Z      = Refl
multPlusDistribLeft m n (S o') =
  rewrite multPlusDistribLeft m n o' in
  rewrite plusCompact m (mult m o') n (mult n o') in Refl

public export
multPlusDistribRight : (m, n, o : Nat) ->
                       mult m (plus n o) = plus (mult m n) (mult m o)
multPlusDistribRight _ _ Z      = Refl
multPlusDistribRight m n (S o') =
  rewrite multPlusDistribRight m n o' in plusSwapLeft m (mult m n) (mult m o')

-------------------
-- mult associative
-------------------

public export
multAssociative : (m, n, o : Nat) -> mult m (mult n o) = mult (mult m n) o
multAssociative _ _ Z      = Refl
multAssociative m n (S o') = rewrite multPlusDistribRight m n (mult n o') in
                             rewrite multAssociative m n o' in Refl

---------------
-- mult neutral
---------------

public export
multLeftOneNeutral : (m : Nat) -> mult (S Z) m = m
multLeftOneNeutral Z      = Refl
multLeftOneNeutral (S m') = rewrite plusLeftOneSucc (mult (S Z) m') in
                            rewrite multLeftOneNeutral m' in Refl

public export
multRightOneNeutral : (m : Nat) -> mult m (S Z) = m
multRightOneNeutral _ = Refl
