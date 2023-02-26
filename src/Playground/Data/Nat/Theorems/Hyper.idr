---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Hyper

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper


-- hyper : Nat -> Nat -> Nat -> Nat
-- hyper Z             _ n      = S n
-- hyper (S Z)         m Z      = m
-- hyper (S (S Z))     _ Z      = Z
-- hyper (S (S (S _))) _ Z      = S Z
-- hyper (S k')        m (S n') = hyper k' m (hyper (S k') m n')
