---------------------
-- Module declaration
---------------------

module Playground.Data.List.Fns.Head

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Data.List.Rels.Proper
import Playground.Rel.Rel

----------------
-- Head function
----------------

public export
head : (xs : List a) -> Proper xs -> a
head (x::_) IsProper = x
