---------------------
-- Module declaration
---------------------

module Fn.Prod

-------------------
-- Internal imports
-------------------

import Data.Prod
import Fn.Comp
import Fn.Eq
import Fn.Id
import Fn.Split
import Rel.Equal

-------------------
-- Function product
-------------------

public export
prod : (f : a -> c) -> (g : b -> d) -> Prod a b -> Prod c d
prod f g = split (f . proj1) (g . proj2)

----------------------------
-- Function product theorems
----------------------------

export
prodAbsorb : FnEq ((prod i j) . (split g h)) (split (i . g) (j . h))
prodAbsorb _ = Refl

export
proj1Absorb : FnEq (i . Prod.proj1) (Prod.proj1 . prod i j)
proj1Absorb _ = Refl

export
proj2Absorb : FnEq (j . Prod.proj2) (Prod.proj2 . prod i j)
proj2Absorb _ = Refl

export
prodFunctor : FnEq (prod (g . h) (i . j)) ((prod g i) . (prod h j))
prodFunctor _ = Refl
