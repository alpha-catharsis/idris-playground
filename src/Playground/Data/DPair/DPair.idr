---------------------
-- Module declaration
---------------------

module Playground.Data.DPair.DPair

----------------------------
-- Dependent Pair definition
----------------------------

namespace Builtin.DPair
  public export
  record DPair a (p : a -> Type) where
    constructor MkDPair
    fst : a
    snd : p fst
