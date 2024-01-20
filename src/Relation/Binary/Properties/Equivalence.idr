---------------------
-- Module declaration
---------------------

module Relation.Binary.Properties.Equivalence

----------
-- Imports
----------

import Relation.Binary.Binary
import Relation.Binary.Properties.Reflexive
import Relation.Binary.Properties.Symmetric
import Relation.Binary.Properties.Transitive

-----------------------
-- Equivalence relation
-----------------------

public export
data Equivalence : (0 a : Type) -> (0 r : HRel a) -> Type where
  [noHints]
  MkEquivalence : ({x : a} -> r x x) ->
                  ({x, y : a} -> r x y -> r y x) ->
                  ({x, y, z : a} -> r x y -> r y z -> r x z) ->
                  Equivalence a r

-------------------------------
-- Equivalence default instance
-------------------------------

%hint
public export
EquivalenceDefault : Reflexive a r => Symmetric a r => Transitive a r =>
                     Equivalence a r
EquivalenceDefault @{MkReflexive reflPrf} @{MkSymmetric symPrf}
                   @{MkTransitive transPrf} =
                     MkEquivalence reflPrf symPrf transPrf
