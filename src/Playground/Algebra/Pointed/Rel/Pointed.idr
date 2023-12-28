---------------------
-- Module declaration
---------------------

module Playground.Algebra.Pointed.Rel.Pointed

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

--------------------
-- Pointed interface
--------------------

public export
data Pointed : (0 s : Type) -> s -> Type where
  IsPointed : (x : s) -> Pointed s x

public export
basepoint : Pointed s x -> s
basepoint (IsPointed x) = x

export
basepointExact : (ps : Pointed s x) -> basepoint ps = x
basepointExact (IsPointed _) = Refl
