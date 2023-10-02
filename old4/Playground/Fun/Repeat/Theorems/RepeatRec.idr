---------------------
-- Module declaration
---------------------

module Playground.Fun.Repeat.Theorems.RepeatRec

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Fun.Prop.Alternate
import Playground.Fun.Repeat.Prop.RepeatRec
import Playground.Fun.Repeat.Repeat
import Playground.Fun.Repeat.Theorems.Repeat

-----------
-- Theorems
-----------

export
repeatAlternate : {0 f : a -> a} -> {0 g : a -> a} -> RepeatRec g f ->
                  Alternate f g
repeatAlternate                        (RepeatOnce f j)       x =
  repeatCntSucc f j x
repeatAlternate                        (RepeatMore rr Z)      x = Refl
repeatAlternate {g = repeat g' (S j')} (RepeatMore rr (S j')) x =
 rewrite repeatAlternate rr (repeat g' j' x) in
 assert_total (cong g' (repeatAlternate (RepeatMore rr j') x))

export
repeatRecInFun : {0 f : a -> a} -> {0 g : a -> a} ->
                 RepeatRec g f -> (j : Nat) -> (x : a) ->
                 f (repeat g j x) = repeat g j (f x)
repeatRecInFun rr Z      x = Refl
repeatRecInFun rr (S j') x = rewrite repeatAlternate rr (repeat g j' x) in
                             cong g (repeatRecInFun rr j' x)
