---------------------
-- Module declaration
---------------------

module Playground.Data.HList.HList

----------
-- Imports
----------

import Playground.Data.List.List

-------------------------------
-- Heterogeneous list data type
-------------------------------

public export
data HList : List Type -> Type where
  HE : HList E
  HC : (x : ty) -> (hs : HList rtys) -> HList (C ty rtys)
