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
  IsIrreflexive : {0 rel : BinHRel a} -> ({0 x : a} -> Not (rel x x)) ->
                  Irreflexive rel

export
%hint
irreflexive : Irreflexive rel -> Not (rel x x)
irreflexive (IsIrreflexive prf) = prf
