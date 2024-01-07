---------------------
-- Module declaration
---------------------

module ScratchPad

-------------------
-- Internal imports
-------------------

import Data.Exp
import Data.List
import Data.Nat
import Data.Prod
import Data.Sum
import Data.Unit
import Fn.Comp
import Fn.ComposeWith
import Fn.Const
import Fn.Either
import Fn.Eq
import Fn.Id
import Fn.Iso
import Fn.Prod
import Fn.Split
import Fn.Sum
import Fn.Transpose
import Rel.Equal

--------------------------
-- List inductive datatype
--------------------------

listOut : List a -> Sum Unit (Prod a (List a))
listOut [] = Inj1 MkUnit
listOut (x::xs) = Inj2 (MkProd x xs)

listIn : Sum Unit (Prod a (List a)) -> List a
listIn = either (const []) (transpose' (::))

listIso : Iso ScratchPad.listOut ScratchPad.listIn
listIso = MkIso listOut listIn (\xs => case xs of
                                         [] => Refl
                                         _::_ => Refl)
                               (\e => case e of
                                        Inj1 MkUnit => Refl
                                        Inj2 (MkProd _ _) => Refl)


--------------------
-- List constructors
--------------------

listC1 : Unit -> List a
listC1 = const []

listC2 : Prod a (List a) -> List a
listC2 = transpose' (::)

------------------------
-- List iso constructors
------------------------

listIsoC1 : Unit -> Sum Unit (Prod a (List a))
listIsoC1 = Inj1

listIsoC2 : Prod a (List a) -> Sum Unit (Prod a (List a))
listIsoC2 = Inj2

--------------------
-- List catamorphism
--------------------

listCata : (out : t -> Sum Unit (Prod a t)) ->
           (g : Sum Unit (Prod a b) -> b) ->
           t -> b
listCata out g = g . sum id (prod id (listCata out g)) . out

-------------------
-- List anamorphism
-------------------

listAna : (in' : Sum Unit (Prod a t) -> t) ->
          (g : b -> Sum Unit (Prod a b)) ->
          b -> t
listAna in' g = in' . sum id (prod id (listAna in' g)) . g

--------------
-- List length
--------------

listLength : List a -> Nat
listLength = listCata listOut (either (const Z) (S . proj2))

-----------------
-- List countdown
-----------------

listCountdown : Nat -> List Nat
listCountdown = listAna listIn (\n => case n of
                                        Z => Inj1 MkUnit
                                        (S n') => Inj2 (MkProd n' n'))

--------------------
-- List hylomorphism
--------------------

listHylo : (out : t -> Sum Unit (Prod a t)) ->
           (in' : Sum Unit (Prod a t) -> t) ->
           (g : Sum Unit (Prod a c) -> c) ->
           (h : b -> Sum Unit (Prod a b)) ->
           b -> c
listHylo out in' g h = g . sum id (prod id (listCata out g . listAna in' h)) . h

----------------------------
-- List hylomorphism example
----------------------------

listHyloEx : Nat -> Nat
listHyloEx = listHylo listOut listIn (either (const Z) (S . proj2))
                                     (\n => case n of
                                        Z => Inj1 MkUnit
                                        (S n') => Inj2 (MkProd n' n'))

-------------------
-- Nat list functor
-------------------

NatListFunctor : Type -> Type
NatListFunctor t = Sum Unit (Prod Nat t)

NatListFAlgebra : Type -> Type
NatListFAlgebra a = NatListFunctor a -> a

NatListFCoalgebra : Type -> Type
NatListFCoalgebra a = a -> NatListFunctor a

natListFunctor : (f : a -> b) -> NatListFunctor a -> NatListFunctor b
natListFunctor f = sum id (prod id f)

natListCata : (g : NatListFAlgebra b) -> List Nat -> b
natListCata g = g . natListFunctor (natListCata g) . listOut

natListAna : (h : NatListFCoalgebra b) -> b -> List Nat
natListAna h = listIn . natListFunctor (natListAna h) . h

natListFunctorId : FnEq (natListFunctor Id.id) Id.id
natListFunctorId (Inj1 _) = Refl
natListFunctorId (Inj2 (MkProd _ _)) = Refl

natListFunctorComp : FnEq (natListFunctor (g . h))
                          (natListFunctor g . natListFunctor h)
natListFunctorComp (Inj1 _) = Refl
natListFunctorComp (Inj2 (MkProd _ _)) = Refl

---------------
-- List functor
---------------

ListFunctor : Type -> Type -> Type
ListFunctor e t = Sum Unit (Prod e t)

listFunctor : (f : a -> b) -> ListFunctor e a -> ListFunctor e b
listFunctor f = sum id (prod id f)

-----------------
-- Prod bifunctor
-----------------

ProdBifunctor : (Prod Type Type) -> Type
ProdBifunctor (MkProd a b) = Prod a b

prodBifunctor : (f : a -> c) -> (g : b -> d) ->
                ProdBifunctor (MkProd a b) -> ProdBifunctor (MkProd c d)
prodBifunctor = prod

prodBifunctorId : FnEq (prodBifunctor Id.id Id.id) Id.id
prodBifunctorId (MkProd _ _) = Refl

prodBifunctorComp : FnEq (prodBifunctor (g . h) (i . j))
                         (prodBifunctor g i . prodBifunctor h j)
prodBifunctorComp (MkProd _ _) = Refl

----------------
-- Sum bifunctor
----------------

SumBifunctor : (Prod Type Type) -> Type
SumBifunctor (MkProd a b) = Sum a b

sumBifunctor : (f : a -> c) -> (g : b -> d) ->
               SumBifunctor (MkProd a b) -> SumBifunctor (MkProd c d)
sumBifunctor = sum

sumBifunctorId : FnEq (sumBifunctor Id.id Id.id) Id.id
sumBifunctorId (Inj1 _ ) = Refl
sumBifunctorId (Inj2 _ ) = Refl

sumBifunctorComp : FnEq (sumBifunctor (g . h) (i . j))
                        (sumBifunctor g i . sumBifunctor h j)
sumBifunctorComp (Inj1 _) = Refl
sumBifunctorComp (Inj2 _) = Refl

-------------------------------
-- Prod-Sum functor composition
-------------------------------

prodSumBifunctor : FnEq ((ScratchPad.prodBifunctor . ScratchPad.sumBifunctor) f)
                        (ScratchPad.prodBifunctor (ScratchPad.sumBifunctor f))
prodSumBifunctor _ = Refl

--------------
-- Nat functor
--------------

NatFunctor : Type -> Type
NatFunctor t = Sum Unit t

NatFAlgebra : Type -> Type
NatFAlgebra a = NatFunctor a -> a

NatFCoalgebra : Type -> Type
NatFCoalgebra a = a -> NatFunctor a

natIn : NatFAlgebra Nat
natIn = either (const Z) S

natOut : NatFCoalgebra Nat
natOut Z = Inj1 MkUnit
natOut (S n) = Inj2 n

natFunctor : (f : a -> b) -> NatFunctor a -> NatFunctor b
natFunctor f = sum id f

natCata : (f : NatFAlgebra a) -> Nat -> a
natCata f = f . natFunctor (natCata f) . natOut

natAna : (g : NatFCoalgebra a) -> a -> Nat
natAna g = natIn . natFunctor (natAna g) . g

natId : Nat -> Nat
natId = natIn . natFunctor id . natOut

---------------
-- Tree functor
---------------

data Tree : Type -> Type where
  Leaf : Tree e
  Branch : e -> Tree e -> Tree e -> Tree e

TreeFunctor : Type -> Type -> Type
TreeFunctor e t = Sum Unit (Prod e (Prod t t))

TreeFAlgebra : Type -> Type -> Type
TreeFAlgebra e a = TreeFunctor e a -> a

TreeFCoalgebra : Type -> Type -> Type
TreeFCoalgebra e a = a -> TreeFunctor e a

treeIn : TreeFAlgebra e (Tree e)
treeIn = either (const Leaf) (\(MkProd x b) => Branch x (proj1 b) (proj2 b))

treeOut : TreeFCoalgebra e (Tree e)
treeOut Leaf = Inj1 MkUnit
treeOut (Branch x lb rb) = Inj2 (MkProd x (MkProd lb rb))

treeIso : Iso ScratchPad.treeIn ScratchPad.treeOut
treeIso = MkIso treeIn treeOut
                (\e => case e of
                         Inj1 MkUnit => Refl
                         Inj2 (MkProd _ (MkProd _ _)) => Refl)
                (\t => case t of
                         Leaf => Refl
                         Branch _ _ _ => Refl)

treeFunctor : (f : a -> b) -> TreeFunctor e a -> TreeFunctor e b
treeFunctor f = sum id (prod id (prod f f))

treeCata : (f : TreeFAlgebra e a) -> Tree e -> a
treeCata f = f . (treeFunctor (treeCata f)) . treeOut

treeAna : (f : TreeFCoalgebra e a) -> a -> Tree e
treeAna g = treeIn . (treeFunctor (treeAna g)) . g

treeHylo : (f : TreeFAlgebra e b) -> (g : TreeFCoalgebra e a) -> a -> b
treeHylo f g = f . (treeFunctor (treeCata f . treeAna g)) . g
