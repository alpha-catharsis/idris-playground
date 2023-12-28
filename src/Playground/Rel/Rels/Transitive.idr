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
  IsTransitive : {rel : BinHRel a} ->
                 ({x : a} -> {y : a} -> rel x y -> rel y z -> rel x z) ->
                 Transitive rel
