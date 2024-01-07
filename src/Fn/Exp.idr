---------------------
-- Module declaration
---------------------

module Fn.Exp

-------------------
-- Internal imports
-------------------

import Data.Exp
import Data.Prod
import Data.Sum
import Data.Unit
import Data.Void
import Fn.Comp
import Fn.Eq
import Fn.Id
import Fn.Iso
import Fn.Either
import Fn.Prod
import Fn.Split
import Fn.Sum
import Rel.Equal

---------------------------
-- Exponential isomorphisms
---------------------------

export
expSumDistrib : Exp a (Sum b c) -> Prod (Exp a b) (Exp a c)
expSumDistrib = split (\f => f . Inj1) (\g => g . Inj2)

export
expSumDistrib' : Prod (Exp a b) (Exp a c) -> Exp a (Sum b c)
expSumDistrib' (MkProd f g) = either f g

export
expProdDistrib : Exp (Prod b c) a -> Prod (Exp b a) (Exp c a)
expProdDistrib = split (\f => proj1 . f) (\g => proj2 . g)

export
expProdDistrib' : Prod (Exp b a) (Exp c a) -> Exp (Prod b c) a
expProdDistrib' (MkProd f g) = split f g

export
expZero : Exp a Void -> Unit
expZero _ = MkUnit

export
expZero' : Unit -> Exp a Void
expZero' _ _ impossible

export
expOneBase : Exp Unit a -> Unit
expOneBase _ = MkUnit

export
expOneBase' : Unit -> Exp Unit a
expOneBase' _ _ = MkUnit

export
expOneExp : Exp a Unit -> a
expOneExp f = f MkUnit

export
expOneExp' : a -> Exp a Unit
expOneExp' x _ = x
