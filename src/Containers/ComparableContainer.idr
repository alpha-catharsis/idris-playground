---------------------
-- Module declaration
---------------------

module Containers.ComparableContainer

-------------------
-- External imports
-------------------

import Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Containers.Container

----------------------
-- Decidable container
----------------------

public export
interface Container t a => ComparableContainer t a | t where
  IncludesPrf : t -> t -> Type
  includesDefinition : {c : t} -> {c' : t} -> ((e : a) -> ContainsPrf c e -> ContainsPrf c' e) -> IncludesPrf c c'
  includesProjection : {c : t} -> {c' : t} -> IncludesPrf c c' -> (e : a) -> ContainsPrf c e -> ContainsPrf c' e
  EquivalentPrf : t -> t -> Type
  equivalentDefinition : {c : t} -> {c' : t} -> IncludesPrf c c' -> IncludesPrf c' c -> EquivalentPrf c c'
  equivalentProjection : {c : t} -> {c' : t} -> EquivalentPrf c c' -> (IncludesPrf c c', IncludesPrf c' c)
  decIncludes : (c : t) -> (c' : t) -> Dec (IncludesPrf c c')

------------
-- Inclusion
------------

public export
includesReflexive : ComparableContainer t a => {c : t} -> IncludesPrf c c
includesReflexive = includesDefinition (\_, contPrf => contPrf)

public export
includesAntisymmetric : ComparableContainer t a => {c : t} -> {c' : t} -> IncludesPrf c c' -> IncludesPrf c' c -> EquivalentPrf c c'
includesAntisymmetric = equivalentDefinition

public export
includesTransitive : ComparableContainer t a => {c : t} -> {c' : t} -> {c'' : t} -> 
                     IncludesPrf c c' -> IncludesPrf c' c'' -> IncludesPrf c c''
includesTransitive inclPrf inclPrf' = let f = includesProjection inclPrf
                                          g = includesProjection inclPrf'
                                      in includesDefinition (\e, contPrf => g e (f e contPrf))

public export
includes : ComparableContainer t a => (c : t) -> (c' : t) -> Bool
includes c c' = isYes (decIncludes c c')

--------------
-- Equivalence
--------------

public export
equivalentReflexive : ComparableContainer t a => {c : t} -> EquivalentPrf c c
equivalentReflexive = equivalentDefinition includesReflexive includesReflexive

public export
equivalentSymmetric : ComparableContainer t a => {c : t} -> {c' : t} -> EquivalentPrf c c' -> EquivalentPrf c' c
equivalentSymmetric eqPrf = let (inclPrf, inclPrf') = equivalentProjection eqPrf
                            in equivalentDefinition inclPrf' inclPrf

public export
equivalentTransitive : ComparableContainer t a => {c : t} -> {c' : t} -> {c'' : t} -> 
                       EquivalentPrf c c' -> EquivalentPrf c' c'' -> EquivalentPrf c c''
equivalentTransitive eqPrf eqPrf' = let (inclPrf1, inclPrf2) = equivalentProjection eqPrf
                                        (inclPrf1', inclPrf2') = equivalentProjection eqPrf'
                                    in equivalentDefinition (includesTransitive inclPrf1 inclPrf1') 
                                                             (includesTransitive inclPrf2' inclPrf2)

public export
decEquivalent : ComparableContainer t a => (c : t) -> (c' : t) -> Dec (EquivalentPrf c c')
decEquivalent c c' = case decIncludes c c' of
  No inclContra => No (\eqPrf => let (inclPrf, _) = equivalentProjection eqPrf in inclContra inclPrf)
  Yes inclPrf => case decIncludes c' c of
    No inclContra' => No (\eqPrf => let (_, inclPrf') = equivalentProjection eqPrf in inclContra' inclPrf')
    Yes inclPrf' => Yes (equivalentDefinition inclPrf inclPrf')

public export
equivalent : ComparableContainer t a => (c : t) -> (c' : t) -> Bool
equivalent c c' = isYes (decEquivalent c c')
