---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Symmetric

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel
import Playground.Rel.Rels.Symmetric

--------------------------------
-- Symmetric equality definition
--------------------------------

export
%hint
symmetricEqual : Symmetric Equal
symmetricEqual = IsSymmetric (\Refl => Refl)
