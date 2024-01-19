---------------------
-- Module declaration
---------------------

module Types.Uninhabited

----------
-- Imports
----------

import Data.Void.Elimination
import Data.Void.Void

-------------------
-- Uninhabited type
-------------------

public export
data Uninhabited : Type -> Type where
  [noHints]
  MkUninhabited : Not a -> Uninhabited a

public export
uninhabited : Uninhabited a => Not a
uninhabited @{MkUninhabited contra} x = contra x

public export
absurd : Uninhabited a => a -> b
absurd @{MkUninhabited contra} x = void (contra x)
