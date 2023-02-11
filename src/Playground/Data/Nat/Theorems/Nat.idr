---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Nat

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat

------------
-- Induction
------------

public export
ind : (f : Nat -> Type) -> (prfZ : f Z) ->
      (prfS : (n : Nat) -> f n -> f (S n)) ->
      (n : Nat) -> f n
ind f prfZ prfS Z      = prfZ
ind f prfZ prfS (S n') = prfS n' (ind f prfZ prfS n')
