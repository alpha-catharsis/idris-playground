---------------------
-- Module declaration
---------------------

module Containers.BoundedContainer

-------------------
-- Internal imports
-------------------

import Containers.Container
import Containers.DecidableContainer

--------------------
-- Bounded container
--------------------

public export
interface DecContainer t a => BoundedContainer t a | t where
  CountPrf : t -> a -> Nat -> Type
  countInjective : (c : t) -> (e : a) -> (n, n' : Nat) -> CountPrf c e n -> CountPrf c e n' -> n = n'
  countWithPrf : (c : t) -> (e : a) -> (n : Nat ** CountPrf c e n)
  notContainsZeroCount : {c : t} -> {e : a} -> Not (ContainsPrf c e) -> CountPrf c e 0
  zeroCountNotContain : {c : t} -> {e : a} -> CountPrf c e 0 -> Not (ContainsPrf c e)
  posCountContains : {c : t} -> {e : a} -> {n : Nat} -> CountPrf c e (S n) -> ContainsPrf c e
  containsPosCount : {c : t} -> {e : a} -> ContainsPrf c e -> (n : Nat ** CountPrf c e (S n))

public export
count : BoundedContainer t a => (c : t) -> (e : a) -> Nat
count c e = fst (countWithPrf c e)
