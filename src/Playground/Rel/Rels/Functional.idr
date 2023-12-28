---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Functional

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

---------------------------------
-- Functional relation definition
---------------------------------

public export
data Functional : Prop (BinHRel a) where
  IsFunctional : {0 rel : BinHRel a} ->
                 ({0 x : a} -> {0 y : a} -> {0 z : a} -> rel x y -> rel x z ->
                  y = z) ->
                 Functional rel

export
%hint
func : Functional rel -> rel x y -> rel x z -> y = z
func (IsFunctional f) relXY relXZ = f relXY relXZ
