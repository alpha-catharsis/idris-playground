---------------------
-- Module declaration
---------------------

module Playground.Fn.Repeat.Theorems.Repeat

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat
import Playground.Fn.Repeat.Repeat

------------------------
-- Basic repeat theorems
------------------------

%hint
public export
repeatZeroId : (f : a -> a) -> repeat f Z x = x
repeatZeroId _ = Refl

%hint
public export
repeatOrdInvariant : (f : a -> a) -> (n : Nat) -> (x : a) ->
                     repeat f n (f x) = f (repeat f n x)
repeatOrdInvariant _ Z      _ = Refl
repeatOrdInvariant f (S n') x = repeatOrdInvariant f n' (f x)

%hint
public export
repeatUnfoldInside : (f : a -> a) -> (n : Nat) -> (x : a) ->
                     repeat f (S n) x = repeat f n (f x)
repeatUnfoldInside _ _ _ = Refl

%hint
public export
repeatUnfoldOutside : (f : a -> a) -> (n : Nat) -> (x : a) ->
                      repeat f (S n) x = f (repeat f n x)
repeatUnfoldOutside f n x = rewrite sym (repeatOrdInvariant f n x)
                            in rewrite repeatUnfoldInside f n x in Refl
