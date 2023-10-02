---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Decidable.Odd

-------------------
-- Internal imports
-------------------

-- import Playground.Basics
-- import Playground.Data.Nat.Nat
-- import Playground.Data.Nat.Prop.Even
-- import Playground.Data.Nat.Prop.Odd
-- import Playground.Data.Nat.Theorems.EvenOdd

----------------
-- Decidable Odd
----------------

-- public export
-- decOdd : (m : Nat) -> Dec (Odd m)
-- decOdd Z         = No (evenNotOdd EvenZ)
-- decOdd (S Z)     = Yes (OddO)
-- decOdd (S (S m)) = case decOdd m of
--   No contra => No (notOddSuccSucc contra)
--   Yes prf   => Yes (OddS prf)
