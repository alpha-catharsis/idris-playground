---------------------
-- Module declaration
---------------------

module Containers.TotalContainer

-------------------
-- Internal imports
-------------------

import Containers.Container

----------------------
-- Decidable container
----------------------

public export
interface Container t a => TotalContainer t a | t where
  totalContainerPrf : (c : t) -> (e : a) -> ContainsPrf c e


