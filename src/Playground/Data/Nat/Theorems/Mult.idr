---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Mult

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

-- import Playground.Basics
-- import Playground.Data.Nat.Nat
-- import Playground.Data.Nat.Ops.Mult
-- import Playground.Data.Nat.Ops.Plus
-- import Playground.Data.Nat.Theorems.Plus
-- import Playground.Fn.Repeat.Repeat
-- import Playground.Fn.Repeat.Theorems.Nat
-- import Playground.Fn.Repeat.Theorems.Repeat

---------------
-- mult neutral
---------------

-- %hint
-- public export
-- multLeftOneNeutral : (n : Nat) -> mult (S Z) n = n
-- multLeftOneNeutral n = rewrite sym (plusLeftOneSucc n) in Refl
