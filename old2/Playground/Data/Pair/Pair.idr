---------------------
-- Module declaration
---------------------

module Playground.Data.Pair.Pair

-------------------
-- Pair declaration
-------------------

public export
data Pair : Type -> Type -> Type where
  MkPair : (x : a) -> (y : b) -> Pair a b
