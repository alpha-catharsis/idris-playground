---------------------
-- Module declaration
---------------------

module Data.List.Contains

----------------
-- Element proof
----------------

public export
data ListContainsPrf : List a -> a -> Type where
  ContainsHere : ListContainsPrf (x::xs) x
  ContainsThere : ListContainsPrf xs x -> ListContainsPrf (y::xs) x
  
public export
Uninhabited (ListContainsPrf [] e) where
  uninhabited _ impossible

public export
{eqContra : Not (x = e)} -> {contContra : Not (ListContainsPrf xs e)} -> Uninhabited (ListContainsPrf (x::xs) e) where
  uninhabited ContainsHere = eqContra Refl
  uninhabited (ContainsThere contPrf) = contContra contPrf
