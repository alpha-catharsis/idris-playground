---------------------
-- Module declaration
---------------------

module Playground.Data.Nat.Ops.Hyper

-------------------
-- Internal imports
-------------------

import Playground.Data.Nat.Nat

------------------
-- hyper operation
------------------

public export
hyper : Nat -> Nat -> Nat -> Nat
hyper Z             _ n      = S n
hyper (S Z)         m Z      = m
hyper (S (S Z))     _ Z      = Z
hyper (S (S (S _))) _ Z      = S Z
hyper (S k')        m (S n') = hyper k' m (hyper (S k') m n')

-- public export
-- hyper : Nat -> Nat -> Nat -> Nat
-- hyper Z             _ n      = S n
-- hyper (S Z)         m Z      = m
-- hyper (S (S Z))     _ Z      = Z
-- hyper (S (S (S _))) _ Z      = S Z
-- hyper (S k')        m (S n') = hyper k' m (hyper (S k') m n')


-- H[0, _, n] = S n
-- H[1, m, Z] = m
-- H[2, _, Z] = 0
-- H[3, _, Z] = 1
-- H[k, m, n] = H[k-1, m, H[k, m, n-1]]

-- k > 0, n > 0
-- H[k, m, n] = H[k-1, m, H[k, m, n-1]]

-- H[1, m, n] = H[0, m, H[1, m, n-1]] =
--            = H[0, m, H[0, m, H[1, m, n-2]]] =
--            = H[0, m, H[0, m, H[0, m, H[1, m, n-3]]]] =
--            = H[... m]

-- H[2, m, n] = H[1, m, H[2, m, n-1]] =
--            = H[1, m, H[1, m, H[2, m, n-2]]] =
--            = H[... Z]

-- H[3, m, n] = H[2, m, H[3, m, n-1]] =
--            = H[2, m, H[2, m, H[3, m, n-2]]] =
--            = H[... S Z]

-- H[4, m, n] = H[3, m, H[4, m, n-1]] =
--            = H[3, m, H[3, m, H[4, m, n-1]] =
--            = H[... S Z]


-- public export
-- hyper' : Nat -> Nat -> Nat -> Nat
-- hyper' Z             _ n = repeat S (S Z) n
-- hyper' (S Z)         m n = repeat S m n
-- hyper' (S (S Z))     m n = repeat (repeat S m) n Z
-- -- hyper' (S (S (S Z))) m n = repeat (repeat (repeat S m) n) (S Z)
-- hyper' _ m n = ?a
