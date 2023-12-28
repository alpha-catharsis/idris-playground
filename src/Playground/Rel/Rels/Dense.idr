---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Dense

-------------------
-- Internal imports
-------------------

import Playground.Data.DPair.DPair
import Playground.Data.Pair.Pair
import Playground.Rel.Rel

----------------------------
-- Dense relation definition
----------------------------

public export
data Dense : Prop (BinHRel a) where
  IsDense : {rel : BinHRel a} ->
            ({x : a} -> {y : a} -> rel x y -> (z : a ** (rel x z, rel z y))) ->
            Dense rel
