---------------------
-- Module declaration
---------------------

module Playground.Rel.Rel

----------
-- Imports
----------

import Playground.Data.HList.HList
import Playground.Data.List.List
import Playground.Decidable.Decidable

-----------
-- Relation
-----------

public export
interface Rel (0 tys : List Type) relTy | relTy where
  RelTy : HList tys -> relTy -> Type

-- public export
-- Rel : List Type -> Type
-- Rel E = Type
-- Rel (C ty rtys) = ty -> Rel rtys

---------------------
-- Decidable Relation
---------------------

public export
interface Rel tys relTy => DecRel tys relTy where
  decRel : (hs : HList tys) -> (r : relTy) -> Dec (RelTy hs r)

-- public export
-- DecRel : (tys : List Type) -> Rel tys -> Type
-- DecRel E prf = Dec prf
-- DecRel (C ty rtys) r = (x : ty) -> DecRel rtys (r x)
