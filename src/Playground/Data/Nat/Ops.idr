---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops

-------------------
-- Internal imports
-------------------

import Playground.Data.Fin.Fin
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Prop.Numeric

----------------
-- Add operation
----------------

public export
add : Nat -> Nat -> Nat
add Z r = r
add (S l) r = S (add l r)

----------------
-- Sub operation
----------------

public export
sub : (l : Nat) -> (r : Nat) -> {auto 0 prf : LTE r l} -> Nat
sub l Z = l
sub Z (S r) impossible
sub (S l) (S r) = sub l r {prf=ltePrev prf}

-----------------
-- Mult operation
-----------------

public export
mult : Nat -> Nat -> Nat
mult Z r = Z
mult (S l) r = add r (mult l r)

