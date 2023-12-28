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
  IsInjective : {rel : BinHRel a} ->
                ({x : a} -> {y : a} -> {z : a} -> rel x y -> rel z y ->
                 x = z) ->
                Injective rel
