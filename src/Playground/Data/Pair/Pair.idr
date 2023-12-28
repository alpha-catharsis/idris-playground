---------------------
-- Module declaration
---------------------

module Playground.Data.Pair.Pair

------------------
-- Pair definition
------------------

namespace Builtin
  public export
  data Pair : Type -> Type -> Type where
    MkPair : (x : a) -> (y : b) -> Pair a b
