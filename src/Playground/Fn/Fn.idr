---------------------
-- Module declaration
---------------------

module Playground.Fn.Fn

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List
import Playground.Data.Void.Void

----------------------
-- Function definition
----------------------

public export
Fn : List Type -> Type -> Type
Fn [] r = r
Fn (a::as) r = a -> Fn as r

----------------------------
-- Unary Function definition
----------------------------

public export
UnyFn : Type -> Type -> Type
UnyFn a b = Fn [a] b

-----------------------------
-- Unary Operation definition
-----------------------------

public export
UnyOp : Type -> Type
UnyOp a = Fn [a] a

------------------------------
-- Binary Operation definition
------------------------------

public export
BinFn : Type -> Type
BinFn a = Fn [a, a] a

-------------------------------
-- Ternary Operation definition
-------------------------------

public export
TernFn : Type -> Type
TernFn a = Fn [a, a, a] a


