---------------------
-- Module declaration
---------------------

module Playground.Data.List.Fns.Tail

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Data.List.Rels.Proper
import Playground.Rel.Rel

----------------
-- Tail function
----------------

public export
tail : (xs : List a) -> Proper xs -> List a
tail (_::xs) IsProper = xs
