---------------------
-- Module declaration
---------------------

module Types.Inhabited

-----------------
-- Inhabited type
-----------------

public export
data Inhabited : Type -> Type where
  [noHints]
  MkInhabited : (x : a) -> Inhabited a

public export
inhabitant : Inhabited a => a
inhabitant @{MkInhabited x} = x
