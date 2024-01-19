---------------------
-- Module declaration
---------------------

module Fn.Sum

-------------------
-- Internal imports
-------------------

import Data.Sum
import Fn.Comp
import Fn.Eq
import Fn.Either
import Fn.Id
import Rel.Equal

---------------
-- Function sum
---------------

public export
sum : (f : a -> c) -> (g : b -> d) -> Sum a b -> Sum c d
sum f g = either (Inj1 . f) (Inj2 . g)

------------------------
-- Function sum theorems
------------------------

export
sumAbsorb : FnEq (either g h . sum i j) (either (g . i) (h . j))
sumAbsorb (Inj1 _) = Refl
sumAbsorb (Inj2 _) = Refl

export
sumFunctor : FnEq (sum (g . h) (i . j)) ((sum g i) . (sum h j))
sumFunctor (Inj1 _) = Refl
sumFunctor (Inj2 _) = Refl
