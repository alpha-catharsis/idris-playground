---------------------
-- Module declaration
---------------------

module Playground.IFace.Uninhabited.Uninhabited

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void

------------------------
-- Uninhabited interface
------------------------

public export
interface Uninhabited t where
  uninhabited : t -> Void

%extern
prim__void : (0 x : Void) -> a

public export
void : (0 x : Void) -> a
void = prim__void

public export
absurd : Uninhabited t => (h : t) -> a
absurd h = void (uninhabited h)

export
Uninhabited Void where
  uninhabited x = x
