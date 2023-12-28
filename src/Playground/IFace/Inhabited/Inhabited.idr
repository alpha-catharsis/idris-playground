---------------------
-- Module declaration
---------------------

module Playground.IFace.Inhabited.Inhabited

----------------------
-- Inhabited interface
----------------------

public export
interface Inhabited t where
  inhabitant : t
