---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Functional

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel
import Playground.Rel.Rels.Functional

---------------------------------
-- Functional equality definition
---------------------------------

export
%hint
functionalEqual : Functional Equal
functionalEqual = IsFunctional (\Refl, Refl => Refl)
