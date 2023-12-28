---------------------
-- Module declaration
---------------------

module Playground.Fn.Fns.Compose

-------------------
-- Internal imports
-------------------

import Playground.Data.HList.HList
import Playground.Data.List.Fns.Append
import Playground.Data.List.List
import Playground.Fn.Fn

-----------------
-- Apply function
-----------------

infixr 9 .

public export
(.) : UnyFn a r -> UnyFn r r' -> UnyFn a r'
(.) f g = \x => g (f x)

public export
compose : {as : List Type} -> Fn as r -> Fn (r::bs) r' -> Fn (as ++ bs) r'
compose {as=[]} f g = g f
compose {as=a'::as'} f g = \x => compose (f x) g
