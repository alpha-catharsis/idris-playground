---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Transitive

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel
import Playground.Rel.Rels.Transitive

---------------------------------
-- Transitive equality definition
---------------------------------

export
%hint
transitiveEqual : Transitive Equal
transitiveEqual = IsTransitive (\Refl, Refl => Refl)
