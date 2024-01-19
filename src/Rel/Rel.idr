---------------------
-- Module declaration
---------------------

module Rel.Rel

------------------
-- Binary relation
------------------

public export
Rel : Type -> Type ->Type
Rel a b = a -> b -> Type
