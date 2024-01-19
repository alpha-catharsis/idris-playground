---------------------
-- Module declaration
---------------------

module Fn.Undistr

-------------------
-- Internal imports
-------------------

import Data.Prod
import Data.Sum
import Fn.Comp
import Fn.Either
import Fn.Eq
import Fn.Id
import Fn.Iso
import Fn.Prod
import Fn.Split
import Fn.Sum
import Rel.Equal

-------------------------
-- Undistribute functions
-------------------------

undistrLeft : Prod a (Sum b c) -> Sum (Prod a b) (Prod a c)
undistrLeft (MkProd x (Inj1 y)) = Inj1 (MkProd x y)
undistrLeft (MkProd x (Inj2 z)) = Inj2 (MkProd x z)

undistrRight : Sum (Prod a b) (Prod a c) -> Prod a (Sum b c)
undistrRight = either (prod id Inj1) (prod id Inj2)

----------------------------------
-- Undistribute functions theorems
----------------------------------

export
undistrIso : Iso Undistr.undistrLeft Undistr.undistrRight
undistrIso = MkIso undistrLeft undistrRight
                   (\(MkProd _ e) => case e of
                     Inj1 _ => Refl
                     Inj2 _ => Refl)
                   (\e => case e of
                     Inj1 (MkProd _ _) => Refl
                     Inj2 (MkProd _ _) => Refl)

export
exchangeLaw : FnEq (either (split f g) (split h k))
                   (split (either f h) (either g k))
exchangeLaw (Inj1 _) = Refl
exchangeLaw (Inj2 _) = Refl
