open import Base

data Symbol : Set where
  ERA : Symbol
  CON : Symbol
  DUP : Symbol

arity : Symbol -> Nat
arity ERA = 0
arity CON = 2
arity DUP = 2

infixr 9 _#_
record UsedPort {len : Nat} (types : Fin len -> Symbol) : Set where
  constructor _#_
  field
    -- this port is of node:
    node : Fin len
    -- this port has this many slots:
    slot : Fin (succ (arity (types node)))

infix 8 port_

data Port {len freeLen : Nat} (types : Fin len → Symbol) : Set where
  free : Fin freeLen → Port types
  port_ : UsedPort types → Port types

record WellConnected {A : Set} (f : A -> A) : Set where
  field
    cycles-back : ∀ x -> f (f x) ≡ x
    not-same : ∀ x -> f x ≢ x

record Graph (len : Nat) (freeLen : Nat) : Set where
  constructor graph
  field
    types : Fin len -> Symbol
    enter : Port {len} {freeLen} types -> Port {len} {freeLen} types
    well-connected : WellConnected enter

-- TODO:
-- Converts a list of nats to a graph. Example:
-- build-graph [(0,1,1),(0,2,2)] ≡ example
--build-graph : (nodes : List (Pair Symbol (Pair Nat (Pair Nat Nat)))) -> Maybe (Graph (len nodes))
--build-graph = {!!}

example-era-era : Graph 2 0
example-era-era =
  graph
    (λ x → ERA)
    (λ{ (port 0F # 0F) → port 1F # 0F ; (port 1F # 0F) → port 0F # 0F})
    (record
      { cycles-back = λ{ (port 0F # 0F) → refl ; (port 1F # 0F) → refl}
      ; not-same = λ{ (port 0F # 0F) () ; (port 1F # 0F) () }
      }
    )

-- Example graph:
-- (a b b)
-- (a c c)
example-con-con : Graph 2 0
example-con-con = graph types enter well-connected where
  types : Fin 2 -> Symbol
  types 0F = CON
  types 1F = CON

  enter : Port {freeLen = 0} types -> Port types 
  enter (port 0F # 0F) = port 1F # 0F
  enter (port 0F # 1F) = port 0F # 2F
  enter (port 0F # 2F) = port 0F # 1F
  enter (port 1F # 0F) = port 0F # 0F
  enter (port 1F # 1F) = port 1F # 2F
  enter (port 1F # 2F) = port 1F # 1F

  well-connected : WellConnected enter
  well-connected = record
    { cycles-back = cycles-back
    ; not-same = not-same }
      where

      cycles-back : (x : Port types) -> enter (enter x) ≡ x
      cycles-back (port 0F # 0F) = refl
      cycles-back (port 0F # 1F) = refl
      cycles-back (port 0F # 2F) = refl
      cycles-back (port 1F # 0F) = refl
      cycles-back (port 1F # 1F) = refl
      cycles-back (port 1F # 2F) = refl

      not-same : (x : Port types) -> Not (enter x ≡ x)
      not-same (port 0F # 0F) ()
      not-same (port 0F # 1F) ()
      not-same (port 0F # 2F) ()
      not-same (port 1F # 0F) ()
      not-same (port 1F # 1F) ()
      not-same (port 1F # 2F) ()

example-con-era : Graph 4 0
example-con-era = graph types enter well-connected where
  types : Fin 4 -> Symbol
  types 0F = ERA
  types 1F = CON
  types 2F = ERA
  types 3F = ERA

  enter : Port {freeLen = 0} types -> Port types
  enter (port 0F # 0F) = port 1F # 0F
  enter (port 1F # 0F) = port 0F # 0F
  enter (port 1F # 1F) = port 2F # 0F
  enter (port 1F # 2F) = port 3F # 0F
  enter (port 2F # 0F) = port 1F # 1F
  enter (port 3F # 0F) = port 1F # 2F

  well-connected : WellConnected enter
  well-connected = record
    { cycles-back = cycles-back
    ; not-same = not-same }
      where

      cycles-back : (x : Port types) -> enter (enter x) ≡ x      
      cycles-back (port 0F # 0F) = refl
      cycles-back (port 1F # 0F) = refl
      cycles-back (port 1F # 1F) = refl
      cycles-back (port 1F # 2F) = refl
      cycles-back (port 2F # 0F) = refl
      cycles-back (port 3F # 0F) = refl

      not-same : (x : Port types) -> Not (enter x ≡ x)
      not-same (port 0F # 0F) ()
      not-same (port 1F # 0F) ()
      not-same (port 1F # 1F) ()
      not-same (port 1F # 2F) ()
      not-same (port 2F # 0F) ()
      not-same (port 3F # 0F) ()

  -- record ActivePair {len freeLen : Nat} {sA sB : Symbol} (g : Graph len freeLen) : Set where
  -- constructor activePair
  -- field
  --   a b : UsedPort (Graph.types g)
  --   path  : Graph.enter g (port a) ≡ (port b)
  --   na≢nb : UsedPort.node a ≢ UsedPort.node b

  --   primaryA : UsedPort.slot a ≡ fz
  --   primaryB : UsedPort.slot b ≡ fz
  
  --   symbolA  : Graph.types g (UsedPort.node a) ≡ sA
  --   symbolB  : Graph.types g (UsedPort.node b) ≡ sB
    
--checkApType : ∀ {len} {g : Graph len} → (symA : Symbol) → (symB : Symbol) → ActivePair g → Set
--checkApType {_} {graph types _ _} symA symB (activePair (port a _) (port b _) _ _ _) = (symA ≡ types a) × (symB ≡ types b)

-- apNotSame : ∀ {sA sB} {len freeLen : Nat} {g : Graph len freeLen} → (ap : ActivePair {len} {freeLen} {sA} {sB} g) → ActivePair.a ap ≢ ActivePair.b ap
-- apNotSame {_} {_} {_} {_} {graph _ _ record { cycles-back = _ ; not-same = not-same }} (activePair a b path _ _ _ _ _) = λ{a≡b → not-same (port a) (trans path (sym (cong {!!} a≡b)))}

-- Port = used | free

-- IDEAS:
-- Patch  = Graph (len) (freeWiresLes)
-- split  : Graph len freeLen → idx → (Graph (len-2) (freeLen+0) × Graph 2 2)   -- prove no connection to patch because arity, cycles, w/e
-- split' : Graph len freeLen → idx → (Graph (len-2) (freeLen+2)   × Graph 2 2) -- because dummy free wire
-- reduce-rule : PatchGraph → PatchGraph
-- join : Graph n m → Graph a b → Graph (n+a) ?

ActivePair : (a b : Symbol) → Set
ActivePair ERA ERA = Graph 2 0
ActivePair _ _ = Graph 2 3

EraActivePair : ActivePair ERA ERA
EraActivePair = example-era-era

anni-rule : ActivePair ERA ERA → Graph 0 0
anni-rule _ = graph (λ()) (λ{ (free ()) ; (port ())}) (record { cycles-back = λ{ (free ()) ; (port ())} ; not-same = λ{ (free ()) ; (port ())} })

net-join : ∀ {len freeLen n} → Graph len freeLen → Graph n freeLen → Graph (len + n) 0
net-join {len} {freeLen} {n} (graph types enter well-connected) (graph types' enter' well-connected') =
  graph
    types''
    enter''
    well-connected''
  where
    to : Fin len ⊎ Fin n → Fin (len + n)
    to = join

    from : Fin (len + n) → Fin len ⊎ Fin n
    from = splitAt

    to∘from : ∀ x → from (to x) ≡ x
    to∘from = splitAt-join len n

    from∘to : ∀ y → to (from y) ≡ y
    from∘to = join-splitAt len n

    types'' : Fin (len + n) → Symbol
    types'' = [ types , types' ]′ ∘ from

    types''-to : ∀ (node : Fin len ⊎ Fin n) → (types'' (to node)) ≡ [ types , types' ]′ node
    types''-to node rewrite to∘from node = refl

    -- enter-free : Port {len} {freeLen} types ⊎ Port {n} {freeLen} types' → (Port {len} {0} types) ⊎ (Port {n} {0} types')
    -- enter-free = ?
    -- enter-free (inj₁ (free f)) = inj₂ ? -- (enter' (free f))
    -- enter-free (inj₁ (port p)) = inj₁ (port p)
    -- enter-free (inj₂ (free f)) = inj₁ {!!}
    -- enter-free (inj₂ (port p)) = inj₂ (port p)

    -- join-port : (Port {len} {0} types) ⊎ (Port {n} {0} types') → Port {len + n} {0} types''
    -- join-port (inj₂ (free x)) = join-port (enter-free (inj₂ (free x)))
    -- join-port (inj₁ (port node # slot)) =
    --   port
    --     (to (inj₁ node)) #
    --     (subst (λ x → Fin (succ (arity x))) (sym (types''-to (inj₁ node))) slot)
    -- join-port (inj₂ (port node # slot)) =
    --   port
    --     (to (inj₂ node)) #
    --     (subst (λ x → Fin (succ (arity x))) (sym (types''-to (inj₂ node))) slot)
    -- to-port = join-port

    break : Port {len + n} {0} types'' → Port {len} {freeLen} types ⊎ Port {n} {freeLen} types'
    break (port node # slot) with from node
    -- is it a free or used port?
    ... | inj₁ p = inj₁ {!!}
    ... | inj₂ p = {!!}

    enter⊎ : Port {len} {freeLen} types ⊎ Port {n} {freeLen} types' → Port {len} {0} types ⊎ Port {n} {0} types'
    enter⊎ (inj₁ (free x)) = {!!}
    enter⊎ (inj₁ (port x)) = {!!}
    enter⊎ (inj₂ (free x)) = {!!}
    enter⊎ (inj₂ (port x)) = {!!}

    ammend : Port {len} {0} types ⊎ Port {n} {0} types' → Port {len + n} {0} types''
    ammend (inj₁ (port node # slot)) =
      port
        to (inj₁ node) #
        subst (λ x → Fin (succ (arity x))) (sym (types''-to (inj₁ node))) slot
    ammend (inj₂ (port node # slot)) =
      port
        to (inj₂ node) #
        subst (λ x → Fin (succ (arity x))) (sym (types''-to (inj₂ node))) slot

    enter'' : Port {len + n} {0} types'' → Port {len + n} {0} types''
    enter'' (free x) = free x
    enter'' p@(port node # slot) = ammend (enter⊎ (break p))

    well-connected'' : WellConnected enter''
    well-connected'' = {!!}

      


-- anni-rule : ∀ {len freeLen} → (g : Graph--  (succ (succ len)) freeLen) → (ap : ActivePair {sA = ERA} {sB = ERA} g) → Graph len freeLen
-- anni-rule {len} (graph types enter record { cycles-back = cycles-back ; not-same = not-same }) ap@(activePair pa@(a # _) pb@(b # _) path na≢nb _ _ _ _) =
--   graph types' enter' well-connected'
--   where
--     an = toNat a
--     bn = toNat b
    
--     rewire : Fin len → Fin (succ (succ len))
--     -- TODO: probably not right
--     rewire f = punchIn a (punchIn (punchOut na≢nb) f)

--     rewire' : ∀ {a b} → {f : Fin (succ (succ len))} → f ≢ a → f ≢ b → a ≢ b → Fin len
--     rewire' = punchOut²

--     types' : Fin len → Symbol
--     types' = types ∘ rewire
  
--     -- a, b ∈ Port types
--     -- a, b ∉ Port types'
--     -- ∀ f : Port types', (enter f) ∉ {a, b}
--     -- ? : (f : Port types) → (f ≢ a) → Port types'    

--     enter' : Port types' → Port types'
--     enter' x = {!!}
--     -- enter' p@(port node # slot) =
--     --   let port' = enter (port (rewire node) # slot)
--     --       port≢a = {!!}
--     --       port≢b = {!!}
--     --   in port (rewire' {f = UsedPort.node port'} port≢a port≢b na≢nb) {!!} 

--     well-connected' : WellConnected enter'
--     well-connected' = {!!}
                   
