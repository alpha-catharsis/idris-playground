---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Symmetric

-------------------
-- Internal imports
-------------------

import Playground.Rel.Rel

--------------------------------
-- Symmetric relation definition
--------------------------------

public export
data Symmetric : Prop (BinHRel a) where
  IsSymmetric : {0 rel : BinHRel a} ->
                ({0 x : a} -> {0 y : a} -> rel x y -> rel y x) -> Symmetric rel

export
-- %hint
sym : Symmetric rel -> rel x y -> rel y x
sym (IsSymmetric f) relXY = f relXY
