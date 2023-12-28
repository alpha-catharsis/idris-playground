---------------------
-- Module declaration
---------------------

module Playground.Fn.Fn

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List

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
BinOp : Type -> Type
BinOp a = Fn [a, a] a

-------------------------------
-- Ternary Operation definition
-------------------------------

public export
TernOp : Type -> Type
TernOp a = Fn [a, a, a] a
