---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Asymmetric

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void
import Playground.Rel.Rel

--------------------------------
-- Asymmetric relation definition
--------------------------------

public export
data Asymmetric : Prop (BinHRel a) where
  IsAsymmetric : {0 rel : BinHRel a} ->
                 ({0 x : a} -> {0 y : a} -> rel x y -> Not (rel y x)) ->
                 Asymmetric rel

export
%hint
asym : Asymmetric rel -> rel x y -> Not (rel y x)
asym (IsAsymmetric f) relXY = f relXY

