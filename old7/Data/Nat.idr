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

---------------------
-- Addition operation
---------------------

public export
plus : Nat -> Nat -> Nat
plus Z n = n
plus (S m) n = S (plus m n)
