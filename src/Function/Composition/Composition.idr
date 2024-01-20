---------------------
-- Module declaration
---------------------

module Function.Composition.Composition

-----------------------
-- Function composition
-----------------------

infixr 9 .

(.) : (b -> c) -> (a -> b) -> (a -> c)
g . f = \x => g (f x)
