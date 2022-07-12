---------------------
-- Module declaration
---------------------

module Playground.Op.NeutralElem

-------------------
-- Internal imports
-------------------

import Playground.Op.BinOp
import Playground.Rel.Equal.Equal

-----------------------------------
-- Binary operation neutral element
-----------------------------------

public export
data LeftNeutralElem : (0 o : BinOp a) -> (0 e : a) -> Type where
  HasLeftNeutralElem : (0 o : BinOp a) -> (0 e : a) ->
                       (lprf : (r : a) -> Equal r (o e r)) ->
                       LeftNeutralElem o e

public export
data RightNeutralElem : (0 o : BinOp a) -> (0 e : a) -> Type where
  HasRightNeutralElem : (0 o : BinOp a) -> (0 e : a) ->
                        (rprf : (r : a) -> Equal r (o r e)) ->
                        RightNeutralElem o e

public export
data NeutralElem : (0 o : BinOp a) -> (0 e : a) -> Type where
  HasNeutralElem : (0 o : BinOp a) -> (0 e : a) ->
                   (lprf : LeftNeutralElem o e) ->
                   (rprf : RightNeutralElem o e) ->
                   NeutralElem o e
