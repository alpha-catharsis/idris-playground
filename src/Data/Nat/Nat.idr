---------------------
-- Module declaration
---------------------

module Data.Nat.Nat

-----------------
-- Nat data type
-----------------

public export
data Nat : Type where
  Z : Nat
  S : Nat -> Nat
