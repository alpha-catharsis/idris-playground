---------------------
-- Module declaration
---------------------

module Playground.Fun.FunExt

-------------------
-- External imports
-------------------

import Builtin

--------------------------
-- function extensionality
--------------------------

public export
funExt : ((x : a) -> f x === g x) -> f === g
funExt _ = believe_me (Refl {x = f === g})
