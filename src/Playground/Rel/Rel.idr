---------------------
-- Module declaration
---------------------

module Playground.Rel.Rel

-------------------
-- Internal imports
-------------------

import Playground.Data.List.List

----------------------
-- Relation definition
----------------------

public export
Rel : List Type -> Type
Rel [] = Type
Rel (a::as) = a -> Rel as

----------------------
-- Property definition
----------------------

public export
Prop : Type -> Type
Prop a = Rel [a]

-----------------------------
-- Binary relation definition
-----------------------------

public export
BinRel : Type -> Type -> Type
BinRel a b = Rel [a, b]

-----------------------------------------
-- Binary homogeneous relation definition
-----------------------------------------

public export
BinHRel : Type -> Type
BinHRel a = Rel [a, a]

------------------------------
-- Ternary relation definition
------------------------------

public export
TernRel : Type -> Type -> Type -> Type
TernRel a b c = Rel [a, b, c]
