---------------------
-- Module declaration
---------------------

module Playground.Data.Fin.Fin

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

------------------
-- Fin declaration
------------------

public export
data Fin : (n : Nat) -> Type where
  FZ : Fin (S k)
  FS : Fin k -> Fin (S k)
