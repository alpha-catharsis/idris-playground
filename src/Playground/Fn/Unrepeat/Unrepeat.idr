---------------------
-- Module declaration
---------------------

module Playground.Fn.Unrepeat.Unrepeat

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LTE
import Playground.Fn.Repeat.Repeat

--------------------
-- Ununrepeat function
--------------------

public export
subtract : (m, n : Nat) -> (0 ltePrf : LTE n m) -> Nat
subtract m      Z      LTEZero       = m
subtract (S m') (S n') (LTESucc prf) = subtract m' n' prf

public export
ununrepeat : (f : a -> a) -> (m : Nat) -> (0 x : a) ->
             (prf : Subset (Nat, a)
                           (\(n,y) => x = repeat f (repeat S n Z) y)) ->
             {auto 0 ltePrf : LTE m (fst (fst prf))} -> a
ununrepeat f m _ (Element (n,y) _) = repeat f (subtract n m ltePrf) y

