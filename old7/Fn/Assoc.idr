---------------------
-- Module declaration
---------------------

module Fn.Assoc

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

--------------------------------
-- Product associative functions
--------------------------------

public export
prodAssocLeft : Prod a (Prod b c) -> Prod (Prod a b) c
prodAssocLeft = split (prod id proj1) (proj2 . proj2)

public export
prodAssocRight : Prod (Prod a b) c -> Prod a (Prod b c)
prodAssocRight = split (proj1 . proj1) (prod proj2 id)

-----------------------------------------
-- Product associative functions theorems
-----------------------------------------

export
prodAssocIso : Iso Assoc.prodAssocLeft Assoc.prodAssocRight
prodAssocIso = MkIso prodAssocLeft prodAssocRight
                     (\(MkProd _ (MkProd _ _)) => Refl)
                     (\(MkProd (MkProd _ _) _) => Refl)

----------------------------
-- Sum associative functions
----------------------------

public export
sumAssocLeft : Sum a (Sum b c) -> Sum (Sum a b) c
sumAssocLeft = either (Inj1 . Inj1) (sum Inj2 id)

public export
sumAssocRight : Sum (Sum a b) c -> Sum a (Sum b c)
sumAssocRight = either (sum id Inj1) (Inj2 . Inj2)

------------------------------------
-- Sum associative functions theorems
------------------------------------

export
sumAssocIso : Iso Assoc.sumAssocLeft Assoc.sumAssocRight
sumAssocIso = MkIso sumAssocLeft sumAssocRight
                    (\e => case e of
                      Inj1 _ => Refl
                      Inj2 e' => case e' of
                        Inj1 _ => Refl
                        Inj2 _ => Refl)
                    (\e => case e of
                      Inj1 e' => case e' of
                        Inj1 _ => Refl
                        Inj2 _ => Refl
                      Inj2 _ => Refl)
