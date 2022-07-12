---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Add

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Op.BinOp
import Playground.Op.NeutralElem
import Playground.Prop.Prop
import Playground.Rel.Equal.Equal

----------------------
-- Addition definition
----------------------

public export
add : Nat -> Nat -> Nat
add Z r = r
add (S j) r = S (add j r)

---------------------------
-- Addition neutral element
---------------------------

public export
addLeftNeutralElem : LeftNeutralElem Add.add Z
addLeftNeutralElem = HasLeftNeutralElem Add.add Z lprf
  where lprf : (r : Nat) -> Equal r (add Z r)
        lprf r = AreEqual
