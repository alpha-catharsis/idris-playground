---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Reflexive

-------------------
-- Internal imports
-------------------

import Playground.Rel.Rel

--------------------------------
-- Reflexive relation definition
--------------------------------

public export
data Reflexive : Prop (BinHRel a) where
  IsReflexive : {0 rel : BinHRel a} -> ({0 x : a} -> rel x x) -> Reflexive rel

export
-- %hint
reflexive : Reflexive rel -> rel x x
reflexive (IsReflexive prf) = prf
