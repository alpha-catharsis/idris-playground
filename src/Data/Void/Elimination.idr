---------------------
-- Module declaration
---------------------

module Data.Void.Elimination

----------
-- Imports
----------

import Data.Void.Void

------------------
-- Void eliminator
------------------

%extern
prim__void : (0 _ : Void) -> a

public export
void : (0 _ : Void) -> a
void = prim__void
