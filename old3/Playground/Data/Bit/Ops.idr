---------------------
-- Module declaration
---------------------

module Playground.Data.Bit.Ops

-------------------
-- Internal imports
-------------------

import Playground.Data.Bit.Bit

------
-- Not
------

public export
not : Bit -> Bit
not O = I
not I = O

-----
-- Or
-----

public export
or : Bit -> Bit -> Bit
or O O = O
or O I = I
or I O = I
or I I = I

------
-- And
------

public export
and : Bit -> Bit -> Bit
and O O = O
and O I = O
and I O = O
and I I = I

------
-- Xor
------

public export
xor : Bit -> Bit -> Bit
xor O O = O
xor O I = I
xor I O = I
xor I I = O
