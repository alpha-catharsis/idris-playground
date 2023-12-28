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
  IsFunctional : {rel : BinHRel a} ->
                 ({x : a} -> {y : a} -> {z : a} -> rel x y -> rel x z ->
                  y = z) ->
                 Functional rel
