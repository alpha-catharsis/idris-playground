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
      (prfS : (m : Nat) -> f m -> f (S m)) ->
      (m : Nat) -> f m
ind f prfZ prfS Z      = prfZ
ind f prfZ prfS (S m') = prfS m' (ind f prfZ prfS m')
