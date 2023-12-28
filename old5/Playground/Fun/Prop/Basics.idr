---------------------
-- Module declaration
---------------------

module Playground.Fun.Prop.Basics

-------------------
-- External imports
-------------------

import Builtin

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Fun.Repeat.Repeat


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

------------
-- Test area
------------

ExistInjective : Type -> Type -> Type
ExistInjective a b = (f : a -> b ** Injective f)

ExistSurjective : Type -> Type -> Type
ExistSurjective a b = (f : a -> b ** Surjective f)

ExistInvertible : Type -> Type -> Type
ExistInvertible a b = (f : a -> b ** (Injective f, Surjective f))

ImpInjective : Type -> Type -> Type
ImpInjective a b = Not (f : a -> b ** Injective f)

ImpSurjective : Type -> Type -> Type
ImpSurjective a b = Not (f : a -> b ** Surjective f)




infix 6 >
infix 6 >~
infix 6 ~~
infix 6 <~
infix 6 <


(>) : Type -> Type -> Type
a > b = (ImpInjective a b, ExistSurjective a b)

(>~) : Type -> Type -> Type
a >~ b = ExistSurjective a b

(~~) : Type -> Type -> Type
a ~~ b = ExistInvertible a b

(<~) : Type -> Type -> Type
a <~ b = ExistInjective a b

(<) : Type -> Type -> Type
a < b = (ExistInjective a b, ImpSurjective a b)


notImpl : (p : (x : a) -> (x' : a) -> Type) ->
          (q : (x : a) -> (x' : a) -> Type) ->
          p x x' -> q x x' -> Not (q x x') -> Not (p x x')
notImpl p q prf1 prf2 contra1 _ = contra1 prf2

data One = MkOne
data Two = MkTwo1 | MkTwo2

oneNotTwo : Not (MkTwo1 = MkTwo2)
oneNotTwo _ impossible

goeTwoOneFun : Two -> One
goeTwoOneFun _ = MkOne

goeTwoOneExistSurjective : ExistSurjective Two One
goeTwoOneExistSurjective = (goeTwoOneFun ** \MkOne => (MkTwo1 ** Refl))

goeTwoOneImpInjective : ImpInjective Two One
goeTwoOneImpInjective (f ** inj) = let xxxx = notImpl (f x = f x') (x = x') (inj MkTwo1 MkTwo2)
 in ?yyy

-- goeTwoOne : Two > One
-- goeTwoOne = (goeTwoOneFun ** (goeTwoOneNotInjective, goeTwoOneSurjective))
