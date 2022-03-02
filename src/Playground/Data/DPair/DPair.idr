---------------------
-- Module declaration
---------------------

module Playground.Data.DPair.DPair

--------------------
-- DPair declaration
--------------------

public export
data DPair : (a : Type) -> (p : a -> Type) -> Type where
  MkDPair : (x : a) -> (prf : p x) -> DPair a p
