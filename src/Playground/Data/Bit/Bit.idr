---------------------
-- Module declaration
---------------------

module Playground.Data.Bit.Bit

-----------------
-- Bit definition
-----------------

public export
data Bit = O | I

--------------------------
-- Bit Show implementation
--------------------------

public export
Show Bit where
  show O = "0"
  show I = "1"

--------------
-- Bit parsing
--------------

public export
data ValidBit : Char -> Type where
  ValidZero : ValidBit '0'
  ValidOne : ValidBit '1'

public export
readBit : (c : Char) -> {auto prf : ValidBit c} -> Bit
readBit _ {prf=ValidZero} = O
readBit _ {prf=ValidOne} = I
readBit _ = ?a

-- public export
-- readBit : (c : Char) -> {auto prf : ValidBit c} -> Bit
-- readBit '0' = O
-- readBit '1' = I
-- readBit _ = ?a

public export
readBitMaybe : Char -> Maybe Bit
readBitMaybe '0' = Just O
readBitMaybe '1' = Just I
readBitMaybe _ = Nothing
