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
data Equal : Rel a b where
  AreEqual : Equal x x
