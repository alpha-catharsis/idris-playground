---------------------
-- Module declaration
---------------------

module Relation.Binary.Equality

----------
-- Imports
----------

import Data.Void.Void
import Relation.Binary.Binary
import Relation.Binary.Properties.Reflexive
import Relation.Binary.Properties.Symmetric
import Relation.Binary.Properties.Transitive

--------------------
-- Equality relation
--------------------

public export
data Equal : Rel a b where
 [search a b]
 Refl : {0 x : a} -> Equal x x

%name Equal prf

namespace Builtin

  infix 6 ===, ~=~, /=

  public export
  (===) : (x : a) -> (y : a) -> Type
  (===) = Equal

  public export
  (~=~) : (x : a) -> (y : b) -> Type
  (~=~) = Equal

  public export
  (/=) : (x : a) -> (y : b) -> Type
  (/=) x y = Not (x = y)

%inline
public export
rewrite__impl : {0 x, y : a} -> (0 p : _) ->
                (0 rule : x = y) -> (1 val : p y) -> p x
rewrite__impl p Refl prf = prf

%rewrite Equal rewrite__impl

---------------------------------
-- Equality equivalence instances
---------------------------------

%hint
public export
EqualReflexive : Reflexive a Equal
EqualReflexive = MkReflexive Refl

%hint
public export
EqualSymmetric : Symmetric a Equal
EqualSymmetric = MkSymmetric (\Refl => Refl)

%hint
public export
EqualTransitive : Transitive a Equal
EqualTransitive = MkTransitive (\Refl, Refl => Refl)
