open import Base

data Symbol : Set where
  ERA : Symbol
  CON : Symbol
  DUP : Symbol

arity : Symbol -> Nat
arity ERA = 1
arity CON = 3
arity DUP = 3

record Port (len : Nat) (types : Fin len -> Symbol) : Set where
  constructor port
  field
    -- this port is of node:
    node : Fin len
    -- this port has this many slots:
    slot : Fin (arity (types node))

record WellConnected {A : Set} (f : A -> A) : Set where
  field
    cycles-back : ∀ x -> f (f x) == x
    not-same : ∀ x -> f x != x


record Graph (len : Nat) : Set where
  constructor graph
  field
    types : Fin len -> Symbol
    enter : Port len types -> Port len types
    well-connected : WellConnected enter

-- TODO:
-- Converts a list of nats to a graph. Example:
-- build-graph [(0,1,1),(0,2,2)] == example
--build-graph : (nodes : List (Pair Symbol (Pair Nat (Pair Nat Nat)))) -> Maybe (Graph (len nodes))
--build-graph = {!!}

-- Example graph:
-- (a b b)
-- (a c c)
example_con_con : Graph 2
example_con_con = graph types enter well-connected where
  types : Fin 2 -> Symbol
  types 0F = CON
  types 1F = CON

  enter : Port 2 types -> Port 2 types 
  enter (port 0F 0F) = port 1F 0F
  enter (port 0F 1F) = port 0F 2F
  enter (port 0F 2F) = port 0F 1F
  enter (port 1F 0F) = port 0F 0F
  enter (port 1F 1F) = port 1F 2F
  enter (port 1F 2F) = port 1F 1F

  well-connected : WellConnected enter
  well-connected = record
    { cycles-back = cycles-back
    ; not-same = not-same }
      where

      cycles-back : (x : Port 2 types) -> enter (enter x) == x
      cycles-back (port 0F 0F) = refl
      cycles-back (port 0F 1F) = refl
      cycles-back (port 0F 2F) = refl
      cycles-back (port 1F 0F) = refl
      cycles-back (port 1F 1F) = refl
      cycles-back (port 1F 2F) = refl

      not-same : (x : Port 2 types) -> Not (enter x == x)
      not-same (port 0F 0F) ()
      not-same (port 0F 1F) ()
      not-same (port 0F 2F) ()
      not-same (port 1F 0F) ()
      not-same (port 1F 1F) ()
      not-same (port 1F 2F) ()

example_con_era : Graph 4
example_con_era = graph types enter well-connected where
  types : Fin 4 -> Symbol
  types 0F = ERA
  types 1F = CON
  types 2F = ERA
  types 3F = ERA

  enter : Port 4 types -> Port 4 types
  enter (port 0F 0F) = port 1F 0F
  enter (port 1F 0F) = port 0F 0F
  enter (port 1F 1F) = port 2F 0F
  enter (port 1F 2F) = port 3F 0F
  enter (port 2F 0F) = port 1F 1F
  enter (port 3F 0F) = port 1F 2F

  well-connected : WellConnected enter
  well-connected = record
    { cycles-back = cycles-back
    ; not-same = not-same }
      where

      cycles-back : (x : Port 4 types) -> enter (enter x) == x      
      cycles-back (port 0F 0F) = refl
      cycles-back (port 1F 0F) = refl
      cycles-back (port 1F 1F) = refl
      cycles-back (port 1F 2F) = refl
      cycles-back (port 2F 0F) = refl
      cycles-back (port 3F 0F) = refl

      not-same : (x : Port 4 types) -> Not (enter x == x)
      not-same (port 0F 0F) ()
      not-same (port 1F 0F) ()
      not-same (port 1F 1F) ()
      not-same (port 1F 2F) ()
      not-same (port 2F 0F) ()
      not-same (port 3F 0F) ()
