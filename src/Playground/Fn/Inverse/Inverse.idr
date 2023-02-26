---------------------
-- Module declaration
---------------------

module Playground.Fn.Inverse.Inverse

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics

-------------------
-- Inverse function
-------------------

public export
inverse : (0 f : b -> a) -> (0 x : a) ->
          (prf : Subset b (\y => x = f y)) ->
          b
inverse _ _ (Element y _) = y