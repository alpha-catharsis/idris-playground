---------------------
-- Module declaration
---------------------

module Playground.Data.List.Props.Includes

-------------------
-- External imports
-------------------

import Decidable.Equality

-----------------
-- Includes proof
-----------------

-- public export
-- data Includes : List a -> List a -> Type where
--   InclNil : Includes [] []
--   InclNil : Includes xs ys -> Includes [] []
--   b : Includes xs ys -> Includes (x::xs) (x::ys)
  
---------------------------------
-- Includes uninhabited instances
---------------------------------

-- export
-- Uninhabited (Includes [] (x::ys)) where
--   uninhabited _ impossible

-- export
-- {contra : Either (Not (x = y)) (Not (Includes xs ys))} -> Uninhabited (Includes (x::xs) (y::ys)) where
--   uninhabited StartsNil impossible
--   uninhabited (StartsNext startsPrf) = case contra of 
--     Left eqContra => eqContra Refl
--     Right startsContra => startsContra startsPrf

---------------------
-- Includes decidable
---------------------

-- export
-- decIncludes : DecEq a => (xs : List a) -> (ys : List a) -> Dec (Includes xs ys)
-- decIncludes [] (y::ys) = No absurd
-- decIncludes xs [] = Yes StartsNil
-- decIncludes (x::xs) (y::ys) = case decEq x y of
--   No eqContra => ?a
--   Yes eqPrf => rewrite eqPrf in case decIncludes xs ys of
--     No startsContra => No absurd
--     Yes startsPrf => Yes (StartsNext startsPrf)
