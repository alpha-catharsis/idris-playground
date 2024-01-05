---------------------
-- Module declaration
---------------------

module Playground.Rel.Rels.Connected

-------------------
-- Internal imports
-------------------

import Playground.Data.Either.Either
import Playground.Data.Void.Void
import Playground.Rel.Equal.Equal
import Playground.Rel.Rel

--------------------------------
-- Connected relation definition
--------------------------------

public export
data Connected : Prop (BinHRel a) where
  IsConnected : {0 rel : BinHRel a} ->
                ({0 x : a} -> {0 y : a} -> x /= y ->
                 Either (rel x y) (rel y x)) ->
                Connected rel

export
%hint
connex : Connected rel -> x /= y -> Either (rel x y) (rel y x)
connex (IsConnected f) neqXY = f neqXY
