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
