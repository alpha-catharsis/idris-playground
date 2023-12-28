---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Reflexive

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel
import Playground.Rel.Rels.Reflexive

--------------------------------
-- Reflexive equality definition
--------------------------------

export
%hint
reflexiveEqual : Reflexive Equal
reflexiveEqual = IsReflexive Refl
