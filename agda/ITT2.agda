open import Base

data Symbol : Set where
  ERA : Symbol
  CON : Symbol
  DUP : Symbol

arity : Symbol -> Nat
arity ERA = 0
arity CON = 2
arity DUP = 2

record Port {len : Nat} (types : Fin len -> Symbol) : Set where
  constructor port
  field
    -- this port is of node:
    node : Fin len
    -- this port has this many slots:
    slot : Fin (succ (arity (types node)))

record WellConnected {A : Set} (f : A -> A) : Set where
  field
    cycles-back : ∀ x -> f (f x) == x
    not-same : ∀ x -> f x ≢ x

record Graph (len : Nat) : Set where
  constructor graph
  field
    types : Fin len -> Symbol
    enter : Port types -> Port types
    well-connected : WellConnected enter

-- TODO:
-- Converts a list of nats to a graph. Example:
-- build-graph [(0,1,1),(0,2,2)] == example
--build-graph : (nodes : List (Pair Symbol (Pair Nat (Pair Nat Nat)))) -> Maybe (Graph (len nodes))
--build-graph = {!!}

example-era-era : Graph 2
example-era-era =
  graph
    (λ x → ERA)
    (λ{ (port 0F 0F) → port 1F 0F ; (port 1F 0F) → port 0F 0F})
    (record
      { cycles-back = λ{ (port 0F 0F) → refl ; (port 1F 0F) → refl}
      ; not-same = λ{ (port 0F 0F) () ; (port 1F 0F) () }
      }
    )

-- Example graph:
-- (a b b)
-- (a c c)
example-con-con : Graph 2
example-con-con = graph types enter well-connected where
  types : Fin 2 -> Symbol
  types 0F = CON
  types 1F = CON

  enter : Port types -> Port types 
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

      cycles-back : (x : Port types) -> enter (enter x) == x
      cycles-back (port 0F 0F) = refl
      cycles-back (port 0F 1F) = refl
      cycles-back (port 0F 2F) = refl
      cycles-back (port 1F 0F) = refl
      cycles-back (port 1F 1F) = refl
      cycles-back (port 1F 2F) = refl

      not-same : (x : Port types) -> Not (enter x == x)
      not-same (port 0F 0F) ()
      not-same (port 0F 1F) ()
      not-same (port 0F 2F) ()
      not-same (port 1F 0F) ()
      not-same (port 1F 1F) ()
      not-same (port 1F 2F) ()

example-con-era : Graph 4
example-con-era = graph types enter well-connected where
  types : Fin 4 -> Symbol
  types 0F = ERA
  types 1F = CON
  types 2F = ERA
  types 3F = ERA

  enter : Port types -> Port types
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

      cycles-back : (x : Port types) -> enter (enter x) == x      
      cycles-back (port 0F 0F) = refl
      cycles-back (port 1F 0F) = refl
      cycles-back (port 1F 1F) = refl
      cycles-back (port 1F 2F) = refl
      cycles-back (port 2F 0F) = refl
      cycles-back (port 3F 0F) = refl

      not-same : (x : Port types) -> Not (enter x == x)
      not-same (port 0F 0F) ()
      not-same (port 1F 0F) ()
      not-same (port 1F 1F) ()
      not-same (port 1F 2F) ()
      not-same (port 2F 0F) ()
      not-same (port 3F 0F) ()

record ActivePair {len : Nat} {sA sB : Symbol} (g : Graph len) : Set where
  constructor activePair
  field
    a b : Port (Graph.types g)
    path  : Graph.enter g a == b
    na≢nb : Port.node a ≢ Port.node b

    primaryA : Port.slot a == fz
    primaryB : Port.slot b == fz
  
    symbolA  : Graph.types g (Port.node a) == sA
    symbolB  : Graph.types g (Port.node b) == sB
    
--checkApType : ∀ {len} {g : Graph len} → (symA : Symbol) → (symB : Symbol) → ActivePair g → Set
--checkApType {_} {graph types _ _} symA symB (activePair (port a _) (port b _) _ _ _) = (symA == types a) × (symB == types b)

apNotSame : ∀ {sA sB} {len : Nat} {g : Graph len} → (ap : ActivePair {len} {sA} {sB} g) → ActivePair.a ap ≢ ActivePair.b ap
apNotSame {_} {_} {_} {graph _ _ record { cycles-back = _ ; not-same = not-same }} (activePair a b path _ _ _ _ _) = λ{a≡b → not-same a (trans path (sym a≡b))}

-- Port = used | free

-- IDEAS:
-- Patch  = Graph (len) (freeWiresLes)
-- split  : Graph len freeLen → idx → (Graph (len-2) (freeLen+0) × Graph 2 2)   -- prove no connection to patch because arity, cycles, w/e
-- split' : Graph len freeLen → idx → (Graph (len-2) (freeLen+2)   × Graph 2 2) -- because dummy free wire
-- reduce-rule : PatchGraph → PatchGraph
-- join : Graph n m → Graph a b → Graph (n+a) ?

anni-rule : ∀ {len} → (g : Graph (succ (succ len))) → (ap : ActivePair {sA = ERA} {sB = ERA} g) → Graph len
anni-rule {len} (graph types enter record { cycles-back = cycles-back ; not-same = not-same }) ap@(activePair pa@(port a _) pb@(port b _) path na≢nb _ _ _ _) =
  graph types' enter' well-connected'
  where
    an = toNat a
    bn = toNat b
    
    rewire : Fin len → Fin (succ (succ len))
    -- TODO: probably not right
    rewire f = punchIn a (punchIn (punchOut na≢nb) f)

    rewire' : ∀ {a b} → {f : Fin (succ (succ len))} → f ≢ a → f ≢ b → a ≢ b → Fin len
    rewire' = punchOut²

    types' : Fin len → Symbol
    types' = types ∘ rewire
  
    -- a, b ∈ Port types
    -- a, b ∉ Port types'
    -- ∀ f : Port types', (enter f) ∉ {a, b}
    -- ? : (f : Port types) → (f ≢ a) → Port types'    

    enter' : Port types' → Port types'
    enter' p@(port node slot) =
      let port' = enter (port (rewire node) slot)
          port≢a = {!!}
          port≢b = {!!}
      in port (rewire' {f = Port.node port'} port≢a port≢b na≢nb) {!!}

    well-connected' : WellConnected enter'
    well-connected' = record
      { cycles-back = λ{ (port node slot) → {!!}}
      ; not-same = λ{ (port node slot) n≡en → {!!} }}
                   
