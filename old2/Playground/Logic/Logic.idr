---------------------
-- Module declaration
---------------------

module Playground.Logic.Logic

-------------------
-- Internal imports
-------------------

import Playground.Data.Pair.Pair
import Playground.Data.Either.Either
import Playground.Data.Void.Void

------------
-- Logic not
------------

public export
Not : Type -> Type
Not p = p -> Void

-----------
-- Logic or
-----------

public export
Or : Type -> Type -> Type
Or lp rp = Either lp rp

------------
-- Logic and
------------

public export
And : Type -> Type -> Type
And lp rp = Pair lp rp

------------
-- Logic xor
------------

public export
Xor : Type -> Type -> Type
Xor lp rp = Or (And lp (Not rp)) (And (Not lp) rp)
