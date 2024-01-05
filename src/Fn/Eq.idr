---------------------
-- Module declaration
---------------------

module Fn.Eq

-------------------
-- Internal imports
-------------------

import Rel.Equal

--------------------
-- function equality
--------------------

public export
0 FnEq : (f : a -> b) -> (g : a -> b) -> Type
FnEq f g = (x : a) -> f x = g x
