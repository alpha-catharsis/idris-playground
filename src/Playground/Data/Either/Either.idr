---------------------
-- Module declaration
---------------------

module Playground.Data.Either.Either

--------------------
-- Either definition
--------------------

public export
data Either : Type -> Type -> Type where
  Left : (x : a) -> Either a b
  Right : (x : b) -> Either a b
