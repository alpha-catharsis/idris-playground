---------------------
-- Module declaration
---------------------

module Playground.Basics

-------------------
-- External imports
-------------------

import Builtin

------
-- Not
------

public export
Not : Type -> Type
Not a = a -> Void

-------------
-- Congruence
-------------

public export
cong : (0 f : t -> u) -> (p : a = b) -> f a = f b
cong f Refl = Refl
