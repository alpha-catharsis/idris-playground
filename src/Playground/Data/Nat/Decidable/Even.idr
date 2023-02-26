---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Decidable.Even

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Prop.Even
import Playground.Data.Nat.Prop.Odd
import Playground.Data.Nat.Theorems.EvenOdd

-----------------
-- Decidable Even
-----------------

public export
decEven : (m : Nat) -> Dec (Even m)
decEven Z         = Yes EvenZ
decEven (S Z)     = No (oddNotEven OddO)
decEven (S (S m)) = case decEven m of
  No contra => No (notEvenSuccSucc contra)
  Yes prf   => Yes (EvenS prf)
