---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Injective

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel
import Playground.Rel.Rels.Injective

--------------------------------
-- Injective equality definition
--------------------------------

export
%hint
injectiveEqual : Injective Equal
injectiveEqual = IsInjective (\Refl, Refl => Refl)
