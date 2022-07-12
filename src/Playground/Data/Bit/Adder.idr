---------------------
-- Module declaration
---------------------

module Playground.Data.Bit.Adder

-------------------
-- Internal imports
-------------------

import Playground.Data.Bit.Bit

--------
-- Adder
--------

public export
adder : Bit -> Bit -> Bit -> (Bit, Bit)
adder O O O = (O, O)
adder O O I = (O, I)
adder O I O = (O, I)
adder O I I = (I, O)
adder I O O = (O, I)
adder I O I = (I, O)
adder I I O = (I, O)
adder I I I = (I, I)
