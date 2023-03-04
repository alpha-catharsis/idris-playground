---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Nat

import Builtin


----------------
-- Nat data type
----------------

public export
data Nat : Type where
  Z : Nat
  S : Nat -> Nat

%name Nat m, n, o, p

-----------------------------
-- Nat builtin representation
-----------------------------

%builtin Natural Nat

-----------------
-- Integer to Nat
-----------------

data Bool = False | True

%inline
intToBool : Int -> Bool
intToBool 0 = False
intToBool x = True

prim__integerToNat : Integer -> Nat
prim__integerToNat i
  = if intToBool (prim__lte_Integer 0 i)
      then believe_me i
      else Z

public export
integerToNat : Integer -> Nat
integerToNat 0 = Z
integerToNat x
  = if intToBool (prim__lte_Integer x 0)
       then Z
       else S (assert_total (integerToNat (prim__sub_Integer x 1)))

%integerLit integerToNat
