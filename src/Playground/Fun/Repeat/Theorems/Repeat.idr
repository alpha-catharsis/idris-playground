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
import Playground.Fun.Id.Id
import Playground.Fun.FunExt
import Playground.Fun.Repeat.Repeat

--------------
-- Tautologies
--------------

public export
repeatSucc : repeat (S n) f x = f (repeat n f x)
repeatSucc = Refl

-------------------
-- Natural Identity
-------------------

public export
repeatEqNat : (m : Nat) -> repeat m S Z = m
repeatEqNat Z      = Refl
repeatEqNat (S m') = cong S (repeatEqNat m')

----------------------
-- Function Identities
----------------------

public export
repeatZeroEqId : (0 f : a -> a) -> repeat Z f = Id.id
repeatZeroEqId f = funExt (\x => Refl)

public export
repeatOneEqFun : (0 f : a -> a) -> repeat (S Z) f = f
repeatOneEqFun f = funExt (\x => Refl)

------------------
-- Repeat Identity
------------------

public export
repeatIdentity : (m : Nat) -> (0 x : a) -> repeat m Id.id x = x
repeatIdentity Z      _ = Refl
repeatIdentity (S m') x = repeatIdentity m' x

-------------------------
-- Successive application
-------------------------

public export
repeatSuccApp : (0 f : a -> a) -> (m : Nat) -> (0 x : a) ->
                repeat (S m) f x = repeat m f (f x)
repeatSuccApp _ Z      _ = Refl
repeatSuccApp f (S m') x = cong f (repeatSuccApp f m' x)

-------
-- Swap
-------

public export
repeatSwap : (0 f : a -> a) -> (m : Nat) -> (0 n : Nat) -> (0 x : a) ->
             repeat m f (repeat n f x) = repeat n f (repeat m f x)
repeatSwap _ Z      _ _ = Refl
repeatSwap f (S m') n x =
  rewrite repeatSwap f m' n x in
  rewrite repeatSuccApp f n (repeat m' f x) in Refl

-----------
-- Swap Nat
-----------

public export
repeatSwapNat : (m : Nat) -> (0 n : Nat) ->
                repeat m S n = repeat n S m
repeatSwapNat Z      n = rewrite repeatEqNat n in Refl
repeatSwapNat (S m') n = rewrite sym (repeatSuccApp S n m') in
                         cong S (repeatSwapNat m' n)

---------------
-- Inner repeat
---------------

public export
repeatInFun : (0 f : a -> a) -> (m : Nat) -> (n : Nat) -> (0 x : a) ->
              f (repeat m (repeat n f) x) = repeat m (repeat n f) (f x)
repeatInFun f Z      n x = Refl
repeatInFun f (S m') n x =
  rewrite repeatSuccApp f n (repeat m' (repeat n f) x) in
  rewrite repeatInFun f m' n x in Refl

public export
repeatInSucc : (0 f : a -> a) -> (m : Nat) -> (n : Nat) -> (0 x : a) ->
               repeat m (repeat (S n) f) x =
               repeat m (repeat n f) (repeat m f x)
repeatInSucc f Z      n x = Refl
repeatInSucc f (S m') n x =
  rewrite repeatInSucc f m' n x in
  rewrite repeatInFun f (S m') n (repeat m' f x) in Refl

public export
repeatInSwap : (0 f : a -> a) -> (m : Nat) -> (n : Nat) -> (0 x : a) ->
               repeat m (repeat n f) x = repeat n (repeat m f) x
repeatInSwap f Z      n x = rewrite repeatZeroEqId f in
                            rewrite repeatIdentity n x in Refl
repeatInSwap f (S m') n x =
  rewrite repeatSuccApp (repeat n f) m' x in
  rewrite repeatInSwap f m' n (repeat n f x) in
  rewrite repeatInSucc f n m' x in Refl
