---------------------
-- Module declaration
---------------------

module Playground.Data.Word.Word

-------------------
-- Internal imports
-------------------

import Playground.Data.Bit.Bit

------------------
-- Word definition
------------------

public export
data Word : Nat -> Type where
  LSB : Bit -> Word (S Z)
  NB : Bit -> Word k -> Word (S k)

--------------------------
-- Word Show implementation
--------------------------

public export
Show (Word k) where
  show (LSB b) = show b
  show (NB b w) = show b ++ show w

--------------
-- Word parsing
--------------

public export
data ValidWord : List Char -> Type where
  WordDigit : (c : Char) -> {auto prf : ValidBit c} -> ValidWord [c]
  WordNextDigit : (c : Char) -> {auto prf : ValidBit c} ->
                  (vw : ValidWord cs) -> ValidWord (c :: cs)

public export
readWord' : (s : List Char) -> {auto prf : ValidWord s} -> (k ** Word k)
readWord' [c] {prf=WordDigit c {prf=prf'}} = (S Z ** LSB (readBit c {prf=prf'}))
readWord' (c :: cs) {prf=WordNextDigit c {prf=prf'} _} = let (k ** w) = readWord' cs
                                                         in (S k ** NB (readBit c {prf=prf'}) w)

public export
readWord : (s : String) -> {auto prf : ValidWord (unpack s)} -> (k ** Word k)
readWord s = readWord' (unpack s)

public export
readWordMaybe : (s : String) -> Maybe (k ** Word k)
readWordMaybe s = go (unpack s)
  where go : (s : List Char) -> Maybe (k ** Word k)
        go [] = Nothing
        go [c] = do
          b <- readBitMaybe c
          pure (S Z ** LSB b)
        go (c :: cs) = do
          (k ** w) <- go cs
          b <- readBitMaybe c
          pure (S k ** NB b w)
