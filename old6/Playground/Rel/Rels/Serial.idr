---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Serial

-------------------
-- Internal imports
-------------------

import Playground.Data.DPair.DPair
import Playground.Rel.Rel

-----------------------------
-- Serial relation definition
-----------------------------

public export
data Serial : Prop (BinHRel a) where
  IsSerial : {0 rel : BinHRel a} -> ((x : a) -> (y : a ** rel x y)) ->
             Serial rel

export
%hint
serial : Serial rel -> (x : a) -> (y : a ** rel x y)
serial (IsSerial f) x = f x
