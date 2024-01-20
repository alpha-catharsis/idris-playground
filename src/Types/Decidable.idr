---------------------
-- Module declaration
---------------------

module Types.Decidable

----------
-- Impoort
----------

import Data.Void.Void
import Types.Inhabited
import Types.Uninhabited

-----------------------
-- Decidable inhabitant
-----------------------

public export
data Dec : Type -> Type where
  No : Not a -> Dec a
  Yes : (x : a) -> Dec a

----------------------
-- Decidable interface
----------------------

public export
data Decidable : Type -> Type where
  [noHints]
  MkDecidable : Dec a -> Decidable a

-------------------------------
-- Inhabited decidable instance
-------------------------------

%hint
public export
DecidableInhabited : Inhabited a => Decidable a
DecidableInhabited @{MkInhabited prf} = MkDecidable (Yes prf)

---------------------------------
-- Uninhabited decidable instance
---------------------------------

%hint
public export
DecidableUninhabited : Uninhabited a => Decidable a
DecidableUninhabited @{MkUninhabited contra} = MkDecidable (No contra)
