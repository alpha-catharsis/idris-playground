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
  IsReflexive : {rel : BinHRel a} -> ({x : a} -> rel x x) -> Reflexive rel
