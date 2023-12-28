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
  IsConnected : {rel : BinHRel a} ->
                ({x : a} -> {y : a} -> x /= y -> Either (rel x y) (rel y x)) ->
                Connected rel
