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
  IsAsymmetric : {rel : BinHRel a} ->
                 ({x : a} -> {y : a} -> rel x y -> Not (rel y x)) ->
                 Asymmetric rel
