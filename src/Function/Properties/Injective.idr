---------------------
-- Module declaration
---------------------

module Function.Properties.Injective

----------
-- Imports
----------

import Relation.Binary.Binary
import Relation.Binary.Equality

---------------------
-- Injective function
---------------------

public export
data Injective : (a -> b) -> Type where
  [noHints]
  MkInjective : (f : a -> b) -> ({x : a} -> {y : a} -> f x = f y -> x = y) ->
                Injective f

public export
inj : (0 f : a -> b) -> Injective f => {x : a} -> {y : a} -> f x = f y -> x = y
inj _ @{MkInjective _ h} = h
