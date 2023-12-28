---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Antisymmetric

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

------------------------------------
-- Antisymmetric relation definition
------------------------------------

public export
data Antisymmetric : Prop (BinHRel a) where
  IsAntisymmetric : {rel : BinHRel a} ->
                    ({x : a} -> {y : a} -> rel x y -> rel y x -> x = y) ->
                    Antisymmetric rel
