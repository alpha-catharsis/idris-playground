---------------------
-- Module declaration
---------------------

module Playground.Data.List.IFaces.Inhabited

-------------------
-- Internal imports
-------------------

import Playground.IFace.Inhabited.Inhabited
import Playground.Data.List.List
import Playground.Rel.Rel

---------------------------------
-- List inhabited implementations
---------------------------------

public export
Inhabited (List a) where
  inhabitant = []

public export
[Singleton] (inh : Inhabited a) => Inhabited (List a) where
  inhabitant = [inhabitant @{inh}]
