---------------------
-- Module declaration
---------------------

module Playground.Fun.Prop.Basics

-------------------
-- External imports
-------------------

import Builtin

---------------------
-- Injective function
---------------------

Injective : {a : Type} -> (a -> b) -> Type
Injective f = (x : a) -> (x' : a) -> (f x = f x') -> x = x'

----------------------
-- Surjective function
----------------------

Surjective : {a, b : Type} -> (a -> b) -> Type
Surjective f = (y : b) -> (x : a ** f x = y)

--------------------
-- Inverse functions
--------------------

LeftInverse : {a : Type} -> (g : b -> a) -> (f : a -> b) -> Type
LeftInverse g f = (x : a) -> g (f x) = x

RightInverse : {b : Type} -> (g : b -> a) -> (f : a -> b) -> Type
RightInverse g f = (y : b) -> f (g y) = y

Inverse : {a, b : Type} -> (g : b -> a) -> (f : a -> b) -> Type
Inverse g f = (LeftInverse g f, RightInverse g f)

---------------------------
-- Inverse helper functions
---------------------------

injective : (g : b -> a) -> (f : a -> b) -> LeftInverse g f -> Injective f
injective g f linvPrf = \x, x', eqPrf => rewrite sym (linvPrf x) in
                                         rewrite sym (linvPrf x') in
                                         rewrite eqPrf in Refl

surjective : (g : b -> a) -> (f : a -> b) -> RightInverse g f -> Surjective f
surjective g f rinvPrf = \y => (g y ** rinvPrf y)

rightInverse : (f : a -> b) -> Surjective f -> (g ** RightInverse g f)
rightInverse f surj = (\y => fst (surj y) ** \y => snd (surj y))

inverse : (f : a -> b) -> Injective f -> Surjective f -> (g ** Inverse g f)
inverse f inj surj = let (g ** rinvPrf) = rightInverse f surj in
  (g ** (\x => inj (g (f x)) x (rinvPrf (f x)), rinvPrf))

