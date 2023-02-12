---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Decidable.LTE

-------------------
-- Internal imports
-------------------

import Playground.Basics
import Playground.Data.Nat.Nat
import Playground.Data.Nat.Rel.LTE
import Playground.Data.Nat.Theorems.Ord

---------------
-- Decidable LTE
---------------

public export
decLTE : (n : Nat) -> (m : Nat) -> Dec (LTE n m)
decLTE Z      m      = Yes LTEZero
decLTE (S n') Z      = No notLeftSuccRightZeroLTE
decLTE (S n') (S m') = case decLTE n' m' of
  No contra => No (notBothNextLTE contra)
  Yes prf   => Yes (LTESucc prf)
