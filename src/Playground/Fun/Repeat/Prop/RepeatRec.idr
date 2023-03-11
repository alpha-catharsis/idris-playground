---------------------
-- Module declaration
---------------------

module Playground.Fun.Repeat.Prop.RepeatRec

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Fun.Repeat.Repeat

-------------------
-- Recursive Repeat
-------------------

public export
data RepeatRec : (a -> a) -> (a -> a) -> Type where
  RepeatOnce : (f : a -> a) -> (j : Nat) -> RepeatRec (repeat f j) f
  RepeatMore : RepeatRec g f -> (j : Nat) -> RepeatRec (repeat g j) f

