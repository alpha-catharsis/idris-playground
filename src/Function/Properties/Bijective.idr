---------------------
-- Module declaration
---------------------

module Function.Properties.Bijective

----------
-- Imports
----------

import Data.Sigma.Sigma
import Function.Properties.Injective
import Function.Properties.Surjective
import Relation.Binary.Binary
import Relation.Binary.Equality

---------------------
-- Bijective function
---------------------

public export
data Bijective : (a -> b) -> Type where
  [noHints]
  MkBijective : (f : a -> b) ->
                ({x : a} -> {y : a} -> f x = f y -> x = y) ->
                ({y : b} -> Sigma a (\x => y = f x)) ->
                Bijective f

-----------------------------
-- Bijective default instance
-----------------------------

public export
BijectiveDefault : Injective f => Surjective f => Bijective f
BijectiveDefault @{MkInjective f h} @{MkSurjective f h'} =
  MkBijective f h h'
