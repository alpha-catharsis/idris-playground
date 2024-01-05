---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Injective

-------------------
-- Internal imports
-------------------

import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

--------------------------------
-- Injective relation definition
--------------------------------

public export
data Injective : Prop (BinHRel a) where
  IsInjective : {0 rel : BinHRel a} ->
                ({0 x : a} -> {0 y : a} -> {0 z : a} -> rel x y -> rel z y ->
                 x = z) ->
                Injective rel

export
%hint
inj : Injective rel -> rel x y -> rel z y -> x = z
inj (IsInjective f) relXY relZY = f relXY relZY
