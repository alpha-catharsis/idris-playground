---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Nat

------------------
-- Nat declaration
------------------

public export
data Nat : Type where
  Z : Nat
  S : Nat -> Nat

