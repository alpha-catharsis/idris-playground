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
import Fn.Prod
import Fn.Split
import Rel.Equal

---------------------
-- transpose function
---------------------

public export
transpose : (Prod a b -> c) -> a -> Exp c b
transpose f = \x, y => f (MkProd x y)

public export
transpose' : (a -> Exp c b) -> Prod a b -> c
transpose' f = \(MkProd x y) => f x y

------------------------------
-- transpose function theorems
------------------------------

export
transposeInv : (f : Prod a b -> c) -> FnEq (transpose' (transpose f)) f
transposeInv f (MkProd _ _) = Refl

export
transposeInv' : (f : a -> Exp c b) -> FnEq (transpose (transpose' f)) f
transposeInv' f x = Refl

export
transposeIso : HIso Transpose.transpose Transpose.transpose'
transposeIso = MkHIso transpose transpose' transposeInv transposeInv'

export
transposeEq : {0 f : Prod a b -> c} -> {0 x : a} -> {0 y : b} ->
              f (MkProd x y) = transpose f x y
transposeEq = Refl

