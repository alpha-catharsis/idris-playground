---------------------
-- Module declaration
---------------------

module Data.List.DecidableContainer

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Containers.Container
import Containers.DecidableContainer
import Data.List.Container
import Data.List.Contains

------------------------------------
-- List decidable container instance
------------------------------------

public export
DecEq a => DecContainer (List a) a where
  decContains [] e = No absurd
  decContains (x::xs) e = case decEq x e of
    No eqContra => case decContains xs e of
      No contConta => No absurd
      Yes contPrf => Yes (ContainsThere contPrf)
    Yes eqPrf => rewrite eqPrf in Yes ContainsHere
