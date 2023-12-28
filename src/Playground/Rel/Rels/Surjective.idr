---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Surjective

-------------------
-- Internal imports
-------------------

import Playground.Data.DPair.DPair
import Playground.Rel.Rel

---------------------------------
-- Surjective relation definition
---------------------------------

public export
data Surjective : Prop (BinHRel a) where
  IsSurjective : {rel : BinHRel a} -> ({y : a} -> (x : a ** rel x y)) ->
                 Surjective rel
