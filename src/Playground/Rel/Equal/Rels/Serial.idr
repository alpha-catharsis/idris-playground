---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Rels.Serial

-------------------
-- Internal imports
-------------------

import Playground.Data.DPair.DPair
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel
import Playground.Rel.Rels.Serial

-----------------------------
-- Serial equality definition
-----------------------------

export
%hint
serialEqual : Serial Equal
serialEqual = IsSerial (\x => (x ** Refl))
