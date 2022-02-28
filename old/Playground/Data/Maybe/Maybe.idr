---------------------
-- Module declaration
---------------------

module Playground.Data.Maybe.Maybe

--------------------
-- Maybe declaration
--------------------

public export
data Maybe : a -> Type where
  Nothing : Maybe a
  Just : (x : a) -> Maybe a
