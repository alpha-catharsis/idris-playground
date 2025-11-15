---------------------
-- Module declaration
---------------------

module Playground.Data.List.Theorems.StartsWith

-------------------
-- Internal imports
-------------------

import Playground.Data.List.Props.Elem
import Playground.Data.List.Props.First
import Playground.Data.List.Props.StartsWith

---------------------
-- StartsWith theorem
---------------------

export
startsWithCons : StartsWith xs ys -> StartsWith (x::xs) (x::ys)
startsWithCons StartsNil = StartsNext StartsNil
startsWithCons (StartsNext startsPrf) = StartsNext (startsWithCons startsPrf)

export
startsWithUncons : StartsWith (x::xs) (x::ys) -> StartsWith xs ys
startsWithUncons (StartsNext startsPrf) = startsPrf

export
startsWithUnappend : {ys, zs : List a} -> StartsWith xs (ys ++ zs) -> StartsWith xs ys
startsWithUnappend {ys=[]} startsPrf = StartsNil
startsWithUnappend {ys=y::ys'} StartsNil impossible
startsWithUnappend {ys=y::ys'} (StartsNext startsPrf) = startsWithCons (startsWithUnappend startsPrf)

-----------------------------
-- StartsWith append theorems
-----------------------------

export
startsWithLeftAppendStartsWith : StartsWith xs ys -> StartsWith (xs ++ zs) ys
startsWithLeftAppendStartsWith StartsNil = StartsNil
startsWithLeftAppendStartsWith (StartsNext startsPrf) = StartsNext (startsWithLeftAppendStartsWith startsPrf)

-----------------------------
-- StartsWith first theorems
-----------------------------

export
firstStartsWith : First x xs -> StartsWith xs [x]
firstStartsWith IsFirst = StartsNext StartsNil
