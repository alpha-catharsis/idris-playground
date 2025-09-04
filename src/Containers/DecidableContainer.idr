---------------------
-- Module declaration
---------------------

module Containers.DecidableContainer

-------------------
-- External imports
-------------------

import Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Containers.Container

----------------------
-- Decidable container
----------------------

public export
interface Container t a => DecContainer t a | t where
  decContains : (c : t) -> (e : a) -> Dec (ContainsPrf c e)

public export
contains : DecContainer t a => (c : t) -> (e : a) -> Bool
contains c e = isYes (decContains c e)

