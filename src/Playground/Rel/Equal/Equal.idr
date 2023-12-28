---------------------
-- Module declaration
---------------------

module Playground.Rel.Equal.Equal

-------------------
-- Internal imports
-------------------

import Playground.Data.Void.Void
import Playground.Rel.Rel

-----------------
-- Equal relation
-----------------

public export
data Equal : BinRel a b where
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
