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
  IsAntisymmetric : {0 rel : BinHRel a} ->
                    ({0 x : a} -> {0 y : a} -> rel x y -> rel y x -> x = y) ->
                    Antisymmetric rel

public export
%hint
antisym : Antisymmetric rel -> rel x y -> rel y x -> x = y
antisym (IsAntisymmetric f) relXY relYX = f relXY relYX
