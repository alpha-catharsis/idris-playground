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
import Playground.Fn.Repeat.Repeat
import Playground.Fn.Repeat.Theorems.Repeat

------------------------
-- Basic repeat theorems
------------------------

%hint
public export
repeatSuccOnZero : (n : Nat) -> repeat S n Z = n
repeatSuccOnZero Z      = Refl
repeatSuccOnZero (S n') = rewrite repeatUnfoldOutside S n' Z
                          in cong S (repeatSuccOnZero n')
