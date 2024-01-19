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
0 Fn2Eq : (f : a -> b -> c) -> (g : a -> b -> c) -> Type
Fn2Eq f g = (x : a) -> (y : b) -> f x y = g x y

public export
0 HFnEq : (f : (a -> b) -> (c -> d)) -> (g : (a -> b) -> (c -> d)) -> Type
HFnEq f g = (h : (a -> b)) -> (x : c) -> f h x = g h x

