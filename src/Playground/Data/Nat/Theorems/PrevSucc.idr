---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.PrevSucc

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Prev
import Playground.Data.Nat.Rel.LT

------------------------------------------
-- Prev and Succ are inverse of each other
------------------------------------------

%hint
public export
SuccPrevIsIdentity : prev (S n) = n
SuccPrevIsIdentity = Refl

%hint
public export
PrevSuccIsIdentity : S (prev (S n)) = S n
PrevSuccIsIdentity = Refl
