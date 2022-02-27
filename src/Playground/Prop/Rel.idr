---------------------
-- Module declaration
---------------------

module Playground.Prop.Rel

------------
-- Reflexive
------------

public export
data Refl : (a -> a -> Type) -> Type where
  IsRefl : {0 p : a -> a -> Type} -> (f : {x : a} -> p x x) -> Refl p

public export
refl : Refl p -> {x : a} -> p x x
refl (IsRefl f) = f {x}

------------
-- Symmetric
------------

public export
data Sym : (a -> a -> Type) -> Type where
  IsSym : {0 p : a -> a -> Type} -> (f : {x : a} -> {y : a} -> p x y -> p y x) -> Sym p

public export
sym : Sym p -> {x : a} -> {y : a} -> p x y -> p y x
sym (IsSym f) prf = f {x} {y} prf

-------------
-- Transitive
-------------

public export
data Trans : (a -> a -> Type) -> Type where
  IsTrans : {0 p : a -> a -> Type} -> (f : {x : a} -> {y : a} -> {z : a} ->
                                           p x y -> p y z -> p x z) -> Trans p

public export
trans : Trans p -> {x : a} -> {y : a} -> {z : a} -> p x y -> p y z -> p x z
trans (IsTrans f) lprf rprf = f {x} {y} {z} lprf rprf

----------------
-- Antisymmetric
----------------

public export
data AntiSym : (a -> a -> Type) -> (a -> a -> Type) -> Type where
  IsAntiSym : {0 p : a -> a -> Type} -> {0 peq : a -> a -> Type} ->
              (f : {x : a} -> {y : a} -> p x y -> p y x -> peq x y) -> AntiSym p peq

public export
antiSym : AntiSym p peq -> {x : a} -> {y : a} -> p x y -> p y x -> peq x y
antiSym (IsAntiSym f) lprf rprf = f {x} {y} lprf rprf
