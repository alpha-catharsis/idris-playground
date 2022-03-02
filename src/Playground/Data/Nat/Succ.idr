---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Succ

-------------------
-- Internal imports
-------------------

import Playground.Data.DPair.DPair
import Playground.Data.Nat.Nat
import Playground.Data.Void.Void
import Playground.Fn.Injective
import Playground.Fn.Surjective
import Playground.Logic.Logic
import Playground.Prop.Prop
import Playground.Rel.Equal.Equal

--------------------
-- Succ is injective
--------------------

-- public export
-- ProvenProp Injective S where
--   prvn = IsInjective S (\AreEqual => AreEqual)

-------------------------
-- Succ is not surjective
-------------------------

-- public export
-- DisprovenProp Surjective S where
--   disp (IsSurjective S f) with (f Z)
--     disp (IsSurjective S f) | MkDPair _ _ impossible
