---------------------
-- Module declaration
---------------------

module Playground.Data.Word.Math

-------------------
-- Internal imports
-------------------

import Playground.Data.Bit.Bit
import Playground.Data.Bit.Adder
import Playground.Data.Word.Bitwise
import Playground.Data.Word.Word

-----------
-- Addition
-----------

public export
addWithCarry : Bit -> Word k -> Word k -> (Bit, Word k)
addWithCarry c (LSB lb) (LSB rb) = let (c', b') = adder c lb rb in (c', LSB b')
addWithCarry c (NB lb lw) (NB rb rw) = let (c', w') = addWithCarry c lw rw
                                           (c'', b') = adder c' lb rb
                                       in (c'', NB b' w')

public export
add : Word k -> Word k -> Word k
add lw rw = snd (addWithCarry O lw rw)

--------------
-- Subtraction
--------------

public export
sub : Word k -> Word k -> Word k
sub lw rw = snd (addWithCarry I lw (not rw))
