---------------------
-- Module declaration
---------------------

module Playground.Fun.Theorems.Alternate

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Fun.Prop.Alternate

-----------------
-- Self alternate
-----------------

export
selfAlternate : (f : a -> a) -> Alternate f f
selfAlternate f x = Refl
