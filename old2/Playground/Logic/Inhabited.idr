---------------------
-- Module declaration
---------------------

module Playground.Logic.Inhabited

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void
import Playground.Logic.Logic

----------------------
-- Inhabited interface
----------------------

public export
interface Inhabited t where
  inhabited : t

------------------------
-- Uninhabited interface
------------------------

public export
interface Uninhabited t where
  uninhabited : Not t

public export
void : (0 x : Void) -> a
void _ impossible

public export
absurd : Uninhabited t => t -> a
absurd h = void (uninhabited h)
