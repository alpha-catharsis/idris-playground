---------------------
-- Module declaration
---------------------

module Playground.Decidable.Decidable

----------
-- Imports
----------

import Playground.Data.Void

----------------------
-- Decidable data type
----------------------

public export
data Dec : Type -> Type where
  No : (contra : Not prop) -> Dec prop
  Yes : (prf : prop) -> Dec prop
