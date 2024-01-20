---------------------
-- Module declaration
---------------------

module Function.Properties.Surjective

----------
-- Imports
----------

import Data.Sigma.Sigma
import Relation.Binary.Binary
import Relation.Binary.Equality

----------------------
-- Surjective function
----------------------

public export
data Surjective : (a -> b) -> Type where
  [noHints]
  MkSurjective : (f : a -> b) -> ({y : b} -> Sigma a (\x => y = f x)) ->
                 Surjective f

public export
surj : (0 f : a -> b) -> Surjective f => {y : b} -> Sigma a (\x => y = f x)
surj _ @{MkSurjective _ h} = h
