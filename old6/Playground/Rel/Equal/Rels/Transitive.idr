---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Transitive

-------------------
-- Internal imports
-------------------

import Playground.IFace.Inhabited.Inhabited
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

export
Inhabited (Transitive Equal) where
  inhabitant = transitiveEqual
