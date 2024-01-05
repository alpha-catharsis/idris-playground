---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.StronglyConnected

-------------------
-- Internal imports
-------------------

import Playground.Data.Either.Either
import Playground.Rel.Rel

-----------------------------------------
-- Strongly Connected relation definition
-----------------------------------------

public export
data StronglyConnected : Prop (BinHRel a) where
  IsStronglyConnected : {0 rel : BinHRel a} ->
                        ((x : a) -> (y : a) ->
                         Either (rel x y) (rel y x)) ->
                        StronglyConnected rel

export
%hint
strongConnex : StronglyConnected rel -> (x : a) -> (y : a) ->
               Either (rel x y) (rel y x)
strongConnex (IsStronglyConnected f) x y = f x y
