---------------------
-- Module declaration
---------------------

module Containers.ProperContainer

-------------------
-- Internal imports
-------------------

import Containers.Container

----------------------
-- Decidable container
----------------------

public export
interface Container t a => ProperContainer t a | t where
  elemWithPrf : (c : t) -> (e : a ** ContainsPrf c e)


