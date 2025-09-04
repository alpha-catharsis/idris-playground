---------------------
-- Module declaration
---------------------

module Containers.NullContainer

-------------------
-- Internal imports
-------------------

import Containers.Container

----------------------
-- Decidable container
----------------------

public export
interface Container t a => NullContainer t a | t where
  totalContainerPrf : (c : t) -> (e : a) -> Not (ContainsPrf c e)


