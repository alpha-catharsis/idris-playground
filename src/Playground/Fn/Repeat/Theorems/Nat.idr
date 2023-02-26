---------------------
-- Module declaration
---------------------

module Playground.Fn.Repeat.Theorems.Nat

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Theorems.Succ
import Playground.Fn.Repeat.Repeat
import Playground.Fn.Repeat.Theorems.Repeat

------------------------
-- Basic repeat theorems
------------------------

%hint
public export
repeatSuccOnZero : (m : Nat) -> repeat S m Z = m
repeatSuccOnZero Z      = Refl
repeatSuccOnZero (S m') = rewrite repeatUnfoldOutside S m' Z
                          in succCong (repeatSuccOnZero m')
