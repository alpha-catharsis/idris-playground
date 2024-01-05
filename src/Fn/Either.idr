---------------------
-- Module declaration
---------------------

module Fn.Either

-------------------
-- Internal imports
-------------------

import Data.Sum
import Fn.Comp
import Fn.Eq
import Fn.Id
import Rel.Equal

------------------
-- Function either
------------------

public export
either : (f : a -> c) -> (g : b -> c) -> Sum a b -> c
either f _ (Inj1 x) = f x
either _ g (Inj2 y) = g y

---------------------------
-- Function either theorems
---------------------------

export
sumLeftCancel : FnEq (either g h . Inj1) g
sumLeftCancel _ = Refl

export
sumRightCancel : FnEq (either g h . Inj2) h
sumRightCancel _ = Refl

export
sumRefl : FnEq (either Inj1 Inj2) Id.id
sumRefl (Inj1 _) = Refl
sumRefl (Inj2 _) = Refl

export
sumFusion : FnEq (f . either g h) (either (f . g) (f . h))
sumFusion (Inj1 _) = Refl
sumFusion (Inj2 _) = Refl
