---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Decidable.LTE

-------------------
-- Internal imports
-------------------

-- import Playground.Basics
-- import Playground.Data.Nat.Nat
-- import Playground.Data.Nat.Rel.LTE
-- import Playground.Data.Nat.Theorems.Ord

---------------
-- Decidable LTE
---------------

-- public export
-- decLTE : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
-- decLTE Z      n      = Yes LTEZero
-- decLTE (S m') Z      = No notLeftSuccRightZeroLTE
-- decLTE (S m') (S n') = case decLTE m' n' of
--   No contra => No (notBothNextLTE contra)
--   Yes prf   => Yes (LTESucc prf)
