---------------------
-- Module declaration
---------------------

module Fn.Swap

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
import Fn.Split
import Rel.Equal

------------------------
-- Function product swap
------------------------

public export
prodSwap : Prod a b -> Prod b a
prodSwap = split proj2 proj1

---------------------------------
-- Function product swap theorems
---------------------------------

export
prodSwapIso : Iso Swap.prodSwap Swap.prodSwap
prodSwapIso = MkIso prodSwap prodSwap (\(MkProd _ _) => Refl)
                    (\(MkProd _ _) => Refl)

--------------------
-- Function sum swap
--------------------

public export
sumSwap : Sum a b -> Sum b a
sumSwap = either Inj2 Inj1

-----------------------------
-- Function sum swap theorems
-----------------------------

export
sumSwapIso : Iso Swap.sumSwap Swap.sumSwap
sumSwapIso = MkIso sumSwap sumSwap
                   (\e => case e of
                     Inj1 _ => Refl
                     Inj2 _ => Refl)
                   (\e => case e of
                     Inj1 _ => Refl
                     Inj2 _ => Refl)
