---------------------
-- Module declaration
---------------------

module Fn.Transpose

-------------------
-- Internal imports
-------------------

import Data.Exp
import Data.Prod
import Fn.Comp
import Fn.Eq
import Fn.Id
import Fn.Iso
import Rel.Equal

---------------------
-- transpose function
---------------------

public export
transpose : (Prod a b -> c) -> a -> Exp c b
transpose f = \x => MkExp (\y => f (MkProd x y))

public export
transpose' : (a -> Exp c b) -> Prod a b -> c
transpose' f = \(MkProd x y) => let MkExp g = f x in g y

------------------------------
-- transpose function theorems
------------------------------

export
transposeInv : (f : Prod a b -> c) -> FnEq (transpose' (transpose f)) f
transposeInv f (MkProd _ _) = Refl

export
transposeInv' : (f : a -> Exp c b) -> FnEq (transpose (transpose' f)) f
transposeInv' f x with (f x)
  transposeInv' f x | MkExp g = Refl

export
transposeIso : Iso2 Transpose.transpose Transpose.transpose'
transposeIso = MkIso2 transpose transpose'
                     (\f => transposeInv f)
                     (\f' => transposeInv' f')
