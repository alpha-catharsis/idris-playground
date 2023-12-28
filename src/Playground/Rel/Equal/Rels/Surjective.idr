---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Surjective

-------------------
-- Internal imports
-------------------

import Playground.Data.DPair.DPair
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel
import Playground.Rel.Rels.Surjective

---------------------------------
-- Surjective equality definition
---------------------------------

export
%hint
surjectiveEqual : Surjective Equal
surjectiveEqual = IsSurjective (\y => (y ** Refl))
