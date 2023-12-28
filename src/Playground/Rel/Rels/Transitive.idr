---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Transitive

-------------------
-- Internal imports
-------------------

import Playground.Rel.Rel

--------------------------------
-- Transitive relation definition
--------------------------------

public export
data Transitive : Prop (BinHRel a) where
  IsTransitive : {0 rel : BinHRel a} ->
                 ({0 x : a} -> {0 y : a} -> {0 z : a} -> rel x y -> rel y z ->
                  rel x z) ->
                 Transitive rel

export
-- %hint
trans : Transitive rel -> rel x y -> rel y z -> rel x z
trans (IsTransitive f) relXY relYZ = f relXY relYZ
