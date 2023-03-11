---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Hyper

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

-- public export
-- hyper : Nat -> Nat -> Nat -> Nat
-- hyper Z             _ n      = S n
-- hyper (S Z)         m Z      = m
-- hyper (S (S Z))     _ Z      = Z
-- hyper (S (S (S _))) _ Z      = S Z
-- hyper (S k')        m (S n') = hyper k' m (hyper (S k') m n')


-- H[0, _, n] = S n
-- H[1, m, Z] = m
-- H[2, _, Z] = 0
-- H[3, _, Z] = 1
-- H[k, m, n] = H[k-1, m, H[k, m, n-1]]

-- k > 0, n > 0
-- H[k, m, n] = H[k-1, m, H[k, m, n-1]]

-- H[1, m, n] = H[0, m, H[1, m, n-1]] =
--            = H[0, m, H[0, m, H[1, m, n-2]]] =
--            = H[0, m, H[0, m, H[0, m, H[1, m, n-3]]]] =
--            = H[... m]

-- H[2, m, n] = H[1, m, H[2, m, n-1]] =
--            = H[1, m, H[1, m, H[2, m, n-2]]] =
--            = H[... Z]

-- H[3, m, n] = H[2, m, H[3, m, n-1]] =
--            = H[2, m, H[2, m, H[3, m, n-2]]] =
--            = H[... S Z]

-- H[4, m, n] = H[3, m, H[4, m, n-1]] =
--            = H[3, m, H[3, m, H[4, m, n-1]] =
--            = H[... S Z]


public export
repeat : (f : a -> a) -> (k : Nat) -> (x : a) -> a
repeat f Z      x = x
repeat f (S k') x = f (repeat f k' x)

public export
hyper' : Nat -> Nat -> Nat -> Nat
hyper' Z             _ n = repeat S (S Z) n
hyper' (S Z)         m n = repeat S m n
hyper' (S (S Z))     m n = repeat (repeat S m) n Z
-- hyper' (S (S (S Z))) m n = repeat (repeat (repeat S m) n) (S Z)
hyper' _ m n = ?a



------------------------
-- hyper basics theorems
------------------------




-------------
-- hyper cong
-------------

-- hyperLeftSuccCong : (k, m, n, o, p : Nat) ->
--                     hyper (S k) m (S n) = hyper (S k) o (S p) ->
--                     hyper (S k) (S m) (S n) = hyper (S k) (S o) (S p)
-- hyperLeftSuccCong Z      m Z      m Z      Refl = Refl
-- hyperLeftSuccCong Z      m (S n') o Z      prf =
--   cong S (cong S ?b)
-- hyperLeftSuccCong Z      m Z      o (S p') prf = ?c
-- hyperLeftSuccCong Z      m (S n') o (S p') prf = ?d
-- hyperLeftSuccCong (S k') m n o p prf = ?dddd



-- si : S m = S n -> m = n
-- si Refl = Refl

-- hyperLeftSuccInjective : (k, m, n, o, p : Nat) ->
--                          hyper (S k) (S m) n = hyper (S k) (S o) p ->
--                          hyper (S k) m n = hyper (S k) o p
-- hyperLeftSuccInjective Z      m Z      m Z      Refl = Refl
-- hyperLeftSuccInjective Z      m (S n') o Z      prf =
--   rewrite hyperLeftSuccInjective Z m n' m n' prf in
--   ?aaaaaaaaa
-- hyperLeftSuccInjective Z      m Z      o (S p') prf = ?c
-- hyperLeftSuccInjective Z      m (S n') o (S p') prf =
--   cong S (hyperLeftSuccInjective Z m n' o p' (si prf))
-- hyperLeftSuccInjective (S k') m n o p prf = ?z

-- hyperLeftCancel : (k, m, n, o : Nat) ->
--                    hyper (S k) m n = hyper (S k) o n ->
--                    m = o
-- hyperLeftCancel k Z Z o prf = Refl


-- hyperLeftSuccCong : (k, m, n, o, p : Nat) ->
--                     hyper k m n = hyper k o p ->
--                     hyper k (S m) n = hyper k (S o) p
-- hyperLeftSuccCong k m Z      o Z      prf = ?a
-- hyperLeftSuccCong k m (S n') o Z      prf = ?b
-- hyperLeftSuccCong k m n      o (S p') prf = ?c
-- hyperLeftSuccCong k m (S n') o (S p') prf = ?d
