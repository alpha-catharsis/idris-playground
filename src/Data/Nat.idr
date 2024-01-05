---------------------
-- Module declaration
---------------------

module Data.Nat

-----------------------------
-- Natural numbers definition
-----------------------------

public export
data Nat : Type where
  Z : Nat
  S : Nat -> Nat
