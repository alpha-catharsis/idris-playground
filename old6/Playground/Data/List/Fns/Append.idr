---------------------
-- Module declaration
---------------------

module Playground.Data.List.Fns.Append

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List

-------------------
-- Append operation
-------------------

infixr 7 ++

public export
(++) : List a -> List a -> List a
[] ++ ys = ys
(x::xs) ++ ys = x::xs ++ ys
