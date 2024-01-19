---------------------
-- Module declaration
---------------------

module Fn.Ap

-------------------
-- Internal imports
-------------------

import Data.Exp
import Data.Prod
import Fn.Comp
import Fn.ComposeWith
import Fn.Eq
import Fn.Id
import Fn.Iso
import Fn.Prod
import Fn.Split
import Fn.Transpose
import Rel.Equal

-----------------
-- apply operator
-----------------

public export
ap : Prod (Exp b a) a -> b
ap (MkProd f x) = f x

--------------------------
-- apply operator theorems
--------------------------

export
apUniv : Fn2Eq k (transpose f) -> FnEq f (Ap.ap . (prod k Id.id))
apUniv eqPrf (MkProd x y) = sym (eqPrf x y)

export
expCancel : FnEq f (Ap.ap . (prod (transpose f) Id.id))
expCancel x = rewrite prodRefl x in Refl

export
expRefl : Fn2Eq (transpose Ap.ap) Id.id
expRefl x y = Refl

export
expFusion : Fn2Eq (transpose (g . (prod f Id.id))) (transpose g . f)
expFusion x y = Refl

export
expAbsorb : Fn2Eq (transpose (f . g)) (composeWith f . transpose g)
expAbsorb x y = Refl

export
expFunctor : Fn2Eq (composeWith (g . h)) (composeWith g . composeWith h)
expFunctor x y = Refl
