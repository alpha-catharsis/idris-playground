---------------------
-- Module declaration
---------------------

module Playground.Fun.Repeat.Theorems.Repeat

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Fun.Repeat.Repeat

--------------
-- Tautologies
--------------

export
repeatOuterFun : f (repeat f j x) = repeat f (S j) x
repeatOuterFun = Refl

export
repeatCntZero : repeat f 0 x = x
repeatCntZero = Refl

export
repeatCntOne : repeat f (S Z) x = f x
repeatCntOne = Refl

---------
-- Basics
---------

export
repeatCntSucc : (f : a -> a) -> (j : Nat) -> (x : a) ->
                repeat f (S j) x = repeat f j (f x)
repeatCntSucc f Z      x = Refl
repeatCntSucc f (S j') x = cong f (repeatCntSucc f j' x)

---------------
-- Value repeat
---------------

export
repeatValCntSwap : (f : a -> a) -> (j : Nat) -> (k : Nat) -> (x : a) ->
                   repeat f j (repeat f k x) = repeat f k (repeat f j x)
repeatValCntSwap f Z      k x = Refl
repeatValCntSwap f (S j') k x =
  rewrite repeatValCntSwap f j' k x in
  rewrite repeatCntSucc f k (repeat f j' x) in Refl

---------------
-- Inner repeat
---------------

export
repeatInCntZero : (f : a -> a) -> (k : Nat) -> (x : a) ->
                  repeat (repeat f 0) k x = x
repeatInCntZero f Z      x = Refl
repeatInCntZero f (S k') x = repeatInCntZero f k' x

export
repeatInCntOne : (f : a -> a) -> (k : Nat) -> (x : a) ->
               repeat (repeat f (S Z)) k x = repeat f k x
repeatInCntOne f Z      x = Refl
repeatInCntOne f (S k') x = cong f (repeatInCntOne f k' x)

export
repeatInFun : (f : a -> a) -> (j : Nat) -> (k : Nat) -> (x : a) ->
              f (repeat (repeat f j) k x) = repeat (repeat f j) k (f x)
repeatInFun f j Z      x = Refl
repeatInFun f j (S k') x =
  rewrite repeatCntSucc f j (repeat (repeat f j) k' x) in
  rewrite repeatInFun f j k' x in Refl

export
repeatInCntSucc : (f : a -> a) -> (j : Nat) -> (k : Nat) -> (x : a) ->
                  repeat (repeat f (S j)) k x =
                  repeat (repeat f j) k (repeat f k x)
repeatInCntSucc f _ Z      x = Refl
repeatInCntSucc f j (S k') x =
  rewrite repeatInCntSucc f j k' x in
  rewrite repeatInFun f j (S k') (repeat f k' x) in Refl

export
repeatInCntSwap : (f : a -> a) -> (j : Nat) -> (k : Nat) -> (x : a) ->
                  repeat (repeat f j) k x = repeat (repeat f k) j x
repeatInCntSwap f Z      k x = repeatInCntZero f k x
repeatInCntSwap f (S j') k x =
  rewrite repeatInCntSucc f j' k x in
  rewrite repeatInCntSwap f j' k (repeat f k x) in
  rewrite repeatCntSucc (repeat f k) j' x in Refl
