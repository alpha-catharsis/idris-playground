---------------------
-- Module declaration
---------------------

module Containers.Container

-----------------
-- Contains proof
-----------------

public export
interface Container t a | t where
  ContainsPrf : t -> a -> Type

