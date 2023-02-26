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
repeatOrdInvariant : (f : a -> a) -> (m : Nat) -> (x : a) ->
                     repeat f m (f x) = f (repeat f m x)
repeatOrdInvariant _ Z      _ = Refl
repeatOrdInvariant f (S m') x = repeatOrdInvariant f m' (f x)

%hint
public export
repeatUnfoldInside : (f : a -> a) -> (m : Nat) -> (x : a) ->
                     repeat f (S m) x = repeat f m (f x)
repeatUnfoldInside _ _ _ = Refl

%hint
public export
repeatUnfoldOutside : (f : a -> a) -> (m : Nat) -> (x : a) ->
                      repeat f (S m) x = f (repeat f m x)
repeatUnfoldOutside f m x = rewrite sym (repeatOrdInvariant f m x)
                            in rewrite repeatUnfoldInside f m x in Refl
