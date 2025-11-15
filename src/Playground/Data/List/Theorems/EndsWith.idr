---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.EndsWith

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.EndsWith
import Playground.Data.List.Props.Last

---------------------------
-- EndsWith append theorems
---------------------------

export
endsWithRightAppendEndsWith : (zs : List a) -> EndsWith xs ys -> EndsWith (zs ++ xs) ys
endsWithRightAppendEndsWith [] EndsSame = EndsSame
endsWithRightAppendEndsWith [] (EndsPrev endsPrf) = EndsPrev endsPrf
endsWithRightAppendEndsWith (z::zs) EndsSame = EndsPrev (endsWithRightAppendEndsWith zs EndsSame)
endsWithRightAppendEndsWith (z::zs) (EndsPrev endsPrf) = EndsPrev (endsWithRightAppendEndsWith zs (EndsPrev endsPrf))

-------------------------
-- EndsWith last theorems
-------------------------

export
lastEndsWith : Last x xs -> EndsWith xs [x]
lastEndsWith LastHere = EndsSame
lastEndsWith (LastThere lastPrf) = EndsPrev (lastEndsWith lastPrf)
