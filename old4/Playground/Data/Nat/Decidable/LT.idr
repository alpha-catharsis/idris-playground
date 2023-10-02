---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Decidable.LT

-------------------
-- Internal imports
-------------------

-- import Playground.Basics
-- import Playground.Data.Nat.Nat
-- import Playground.Data.Nat.Rel.LT
-- import Playground.Data.Nat.Theorems.Ord

---------------
-- Decidable LT
---------------

-- public export
-- decLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
-- decLT Z      Z      = No notLTEq
-- decLT Z      (S n') = Yes LTZero
-- decLT (S m') Z      = No notLeftSuccRightZeroLT
-- decLT (S m') (S n') = case decLT m' n' of
--   No contra => No (notBothNextLT contra)
--   Yes prf   => Yes (LTSucc prf)
