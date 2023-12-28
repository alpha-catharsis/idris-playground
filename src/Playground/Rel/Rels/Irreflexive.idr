---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Irreflexive

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void
import Playground.Rel.Rel

----------------------------------
-- Irreflexive relation definition
----------------------------------

public export
data Irreflexive : Prop (BinHRel a) where
  IsIrreflexive : {rel : BinHRel a} -> ({x : a} -> Not (rel x x)) ->
                  Irreflexive rel
