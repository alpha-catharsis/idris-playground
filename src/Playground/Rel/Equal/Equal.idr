---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Equal

-------------------
-- Internal imports
-------------------

import Playground.Rel.Rel

-------------------
-- Equal definition
-------------------

public export
data Equal : a -> b -> Type where
  AreEqual : Equal x x
