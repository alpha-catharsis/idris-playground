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
  IsSymmetric : {rel : BinHRel a} ->
                ({x : a} -> {y : a} -> rel x y -> rel y x) -> Symmetric rel
