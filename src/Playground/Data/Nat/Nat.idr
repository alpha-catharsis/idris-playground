---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Nat

-----------------
-- Nat definition
-----------------

public export
data Nat : Type where
  Z : Nat
  S : Nat -> Nat
