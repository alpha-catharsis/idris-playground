---------------------
-- Module declaration
---------------------

module Data.List.Container

-------------------
-- Internal imports
-------------------

import Containers.Container
import Data.List.Contains

--------------------------
-- List container instance
--------------------------

public export
Container (List a) a where
  ContainsPrf = ListContainsPrf
