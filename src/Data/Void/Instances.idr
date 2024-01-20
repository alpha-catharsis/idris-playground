---------------------
-- Module declaration
---------------------

module Data.Void.Instances

----------
-- Imports
----------

import Data.Void.Void
import Function.Identity
import Types.Uninhabited

----------------------------
-- Void uninhabited instance
----------------------------

%hint
public export
uninhabitedVoid : Uninhabited Void
uninhabitedVoid = MkUninhabited id
