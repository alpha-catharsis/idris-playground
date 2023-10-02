---------------------
-- Module declaration
---------------------

module Playground.Fun.Prop.Alternate

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics

------------
-- Alternate
------------

public export
Alternate : {a : Type} -> (a -> a) -> (a -> a) -> Type
Alternate f g = (x : a) -> f (g x) = g (f x)

