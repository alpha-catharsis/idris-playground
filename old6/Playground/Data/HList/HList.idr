---------------------
-- Module declaration
---------------------

module Playground.Data.HList.HList

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List

--------------------------------
-- Heterogeneous List definition
--------------------------------

infixr 7 ::

public export
data HList : List Type -> Type where
  Nil : HList []
  (::) : (x : a) -> HList as -> HList (a::as)

%name HList as, bs, cs, ds
