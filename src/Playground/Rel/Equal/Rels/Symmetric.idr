---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Symmetric

-------------------
-- Internal imports
-------------------

import Playground.IFace.Inhabited.Inhabited
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

export
Inhabited (Symmetric Equal) where
  inhabitant = symmetricEqual
