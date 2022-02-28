---------------------
-- Module declaration
---------------------

module Playground.Data.Bool.Equal

-------------------
-- Internal imports
-------------------

import Playground.Data.Bool.Bool
import Playground.Data.Void.Void
import Playground.Decidable.Decidable
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

-----------------------------
-- Bool DecRel implementation
-----------------------------

public export
notEqualFalseTrue : Equal False True -> Void
notEqualFalseTrue _ impossible

public export
notEqualTrueFalse : Equal True False -> Void
notEqualTrueFalse _ impossible

public export
DecRel Bool Bool Equal where
  decRel False False = Yes AreEqual
  decRel False True = No notEqualFalseTrue
  decRel True False = No notEqualTrueFalse
  decRel True True = Yes AreEqual
