---------------------
-- Module declaration
---------------------

module Playground.Data.List.Rels.Proper.Rels.Decidable

-------------------
-- Internal imports
-------------------

import Playground.IFace.Uninhabited.Uninhabited
import Playground.Data.List.List
import Playground.Data.List.Rels.Proper.IFaces.Uninhabited
import Playground.Data.List.Rels.Proper.Proper
import Playground.Data.Void.Void
import Playground.Rel.Decidable.Decidable
import Playground.Rel.Rel

---------------------------
-- Proper decision function
---------------------------

public export
decProper : (xs : List a) -> Dec (Proper xs)
decProper [] = No absurd
decProper (_::_) = Yes IsProper
