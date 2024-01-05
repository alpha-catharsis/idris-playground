---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Injective

-------------------
-- Internal imports
-------------------

import Playground.IFace.Inhabited.Inhabited
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

export
Inhabited (Injective Equal) where
  inhabitant = injectiveEqual
