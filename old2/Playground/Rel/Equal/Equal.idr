---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Equal

-------------------
-- Internal imports
-------------------

import Playground.Rel.Rel

-------------------
-- Equal definition
-------------------

public export
data Equal : a -> b -> Type where
  AreEqual : Equal x x

%inline
public export
rewrite__impl : {0 x, y : a} -> (0 p : _) ->
                (0 rule : Equal x y) -> (1 val : p y) -> p x
rewrite__impl p AreEqual prf = prf

%rewrite Equal rewrite__impl
