---------------------
-- Module declaration
---------------------

module Inhabited

----------------------
-- Inhabited interface
----------------------

public export
interface Inhabited a where
  inhabitant : a
