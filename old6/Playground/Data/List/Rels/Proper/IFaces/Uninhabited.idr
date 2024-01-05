---------------------
-- Module declaration
---------------------

module Playground.Data.List.Rels.Proper.IFaces.Uninhabited

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Data.List.Rels.Proper.Proper
import Playground.Data.Void.Void
import Playground.IFace.Uninhabited.Uninhabited
import Playground.Rel.Rel

------------------------------------
-- Proper uninhabited implementation
------------------------------------

public export
Uninhabited (Proper []) where
 uninhabited _ impossible
