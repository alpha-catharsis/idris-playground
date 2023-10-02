---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Theorems.Pow

-------------------
-- External imports
-------------------

import Builtin

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Ops.Hyper
import Playground.Data.Nat.Ops.Mult
import Playground.Data.Nat.Ops.Plus
import Playground.Data.Nat.Ops.Pow
import Playground.Data.Nat.Ops.Succ
import Playground.Data.Nat.Theorems.Mult
import Playground.Data.Nat.Theorems.Plus
import Playground.Data.Nat.Theorems.Succ

----------------
-- power to zero
----------------

-- public export
-- powToZeroIsOne : (b : Nat) -> pow b Z = succ Z
-- powToZeroIsOne _ = Refl

---------------
-- power to one
---------------

-- public export
-- powToOneIsSame : (b : Nat) -> pow b (succ Z) = b
-- powToOneIsSame _ = Refl

----------------
-- power of zero
----------------

-- public export
-- powOfZeroIsOne : (m : Nat) -> pow Z (succ m) = Z
-- powOfZeroIsOne Z      = Refl
-- powOfZeroIsOne (S m') = rewrite multLeftZeroAbsorb (mult Z (pow Z m')) in Refl

------------------
-- power mult succ
------------------

-- powLeftMultSucc : (b, m : Nat) -> mult b (pow b m) = pow b (succ m)
-- powLeftMultSucc _ _ = Refl

-- powRightMultSucc : (b, m : Nat) -> mult (pow b m) b = pow b (succ m)
-- powRightMultSucc b m = rewrite multCommutative (pow b m) b in
--                        powLeftMultSucc b m

----------------
-- power to plus
----------------

-- public export
-- powToPlus : (b, m, n : Nat) -> pow b (plus m n) = mult (pow b m) (pow b n)
-- powToPlus b m      Z      = Refl
-- powToPlus b Z      (S n') = rewrite multLeftOneNeutral (pow b (succ n')) in
--                             rewrite plusLeftZeroNeutral n' in Refl
-- powToPlus b (S m') (S n') = ?a (powToPlus b m' n')

-- pow b (plus m' n') = mult (pow b m') (pow b n') ->
-- pow b (succ (plus (succ m') n')) = mult (pow b (succ m')) (pow b (succ n'))

-- pow b (succ (plus (succ m') n')) = mult (pow b (succ m')) (pow b (succ n'))

-----------------
-- power to power
-----------------

-- public export
-- powToPow : (b, m, n : Nat) -> pow (pow b m) n = pow (mult m n)

----------------
-- power of mult
----------------

-- public export
-- powOfMult : (b, c, m : Nat) -> pow (mult b c) m = mult (pow b n) (pow c n)
