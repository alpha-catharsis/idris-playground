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
  IsDense : {0 rel : BinHRel a} ->
            ({0 x : a} -> {0 y : a} -> rel x y ->
             (z : a ** (rel x z, rel z y))) ->
            Dense rel

export
%hint
dense : Dense rel -> rel x y -> (z : a ** (rel x z, rel z y))
dense (IsDense f) relXY = f relXY
