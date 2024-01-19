---------------------
-- Module declaration
---------------------

module Fn.Split

-------------------
-- Internal imports
-------------------

import Data.Prod
import Fn.Comp
import Fn.Eq
import Fn.Id
import Rel.Equal

-----------------
-- Function split
-----------------

public export
split : (f : a -> b) -> (g : a -> c) -> a -> Prod b c
split f g x = MkProd (f x) (g x)

--------------------------
-- Function split theorems
--------------------------

export
prodRefl : FnEq (split Prod.proj1 Prod.proj2) Id.id
prodRefl (MkProd _ _) = Refl

export
prodLeftCancel : FnEq (Prod.proj1 . split f g) f
prodLeftCancel _ = Refl

export
prodRightCancel : FnEq (Prod.proj2 . split f g) g
prodRightCancel _ = Refl

export
prodFusion : FnEq (split g h . f) (split (g . f) (h . f))
prodFusion _ = Refl

export
univ1 : FnEq k (split f g) -> FnEq (Prod.proj1 . k) f
univ1 eqPrf x = rewrite eqPrf x in Refl

export
univ2 : FnEq k (split f g) -> FnEq (Prod.proj2 . k) g
univ2 eqPrf x = rewrite eqPrf x in Refl

export
univ' : Prod (FnEq (Prod.proj1 . k) f) (FnEq (Prod.proj2 . k) g) ->
        FnEq k (split f g)
univ' (MkProd eqPrf1 eqPrf2) x =
  rewrite sym (eqPrf1 x) in
  rewrite sym (eqPrf2 x) in
  rewrite prodRefl (k x) in Refl
