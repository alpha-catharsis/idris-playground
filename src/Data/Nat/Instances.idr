---------------------
-- Module declaration
---------------------

module Data.Nat.Instances

----------
-- Imports
----------

import Data.Nat.Nat
import Types.Inhabited

-------------------------
-- Nat inhabited instance
-------------------------

%hint
public export
InhabitedNat : Inhabited Nat
InhabitedNat = MkInhabited Z

