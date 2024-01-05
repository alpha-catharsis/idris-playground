---------------------
-- Module declaration
---------------------

module Playground.Data.List.Rels.Proper.Proper

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Data.Void.Void
import Playground.Rel.Rel

-----------------------
-- Proper list property
-----------------------

public export
data Proper : Prop (List a) where
  IsProper : Proper (x::xs)

-----------------------
-- Empty list property
-----------------------

public export
Empty : Prop (List a)
Empty xs = Not (Proper xs)
