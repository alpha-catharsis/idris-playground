---------------------
-- Module declaration
---------------------

module Fn.Const

-------------------
-- Internal imports
-------------------

import Fn.Comp
import Rel.Equal

--------------------
-- Constant function
--------------------

public export
const : a -> b -> a
const x _ = x

-----------------------------
-- Constant function theorems
-----------------------------

constLeftNeutral : {f : a -> b} -> {x : a} -> {z : c} ->
                   (const c . f) x = const c x
constLeftNeutral = Refl
