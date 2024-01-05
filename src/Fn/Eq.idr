---------------------
-- Module declaration
---------------------

module Fn.Eq

-------------------
-- Internal imports
-------------------

import Data.Nat
import Rel.Equal

--------------------
-- function equality
--------------------

public export
0 FnEq : (f : a -> b) -> (g : a -> b) -> Type
FnEq f g = (x : a) -> f x = g x

public export
0 FnEq2 : (f : (a -> b) -> (c -> d)) -> (g : (a -> b) -> (c -> d)) -> Type
FnEq2 f g = (h : (a -> b)) -> (x : c) -> f h x = g h x


