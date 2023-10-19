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

data Port {len : Nat} (freeLen : Nat) (types : Fin len → Symbol) : Set where
  free : Fin freeLen → Port {len} freeLen types
  port_ : UsedPort types → Port {len} freeLen types

record WellConnected {A : Set} (f : A → A) : Set where
  field
    cycles-back : ∀ x -> f (f x) ≡ x
    not-same : ∀ x -> f x ≢ x

  injective : ∀ {i j} → i ≢ j → f i ≢ f j
  injective {i} {j} i≢j fi≡fj = i≢j i≡j
    where
    open ≡-Reasoning
    i≡j : i ≡ j
    i≡j = begin
      i         ≡⟨ sym (cycles-back i) ⟩
      f (f i)   ≡⟨ cong f fi≡fj ⟩
      f (f j)   ≡⟨ cycles-back j ⟩
      j         ∎



record Graph (len : Nat) (freeLen : Nat) : Set where
  constructor graph
  C = Fin len
  field
    types : C -> Symbol
    enter : Port -> Port 
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
--  /--<|===|>--\
--  \-----------/
example-con-con : Graph 2 0
example-con-con = graph types enter well-connected where
  types : Fin 2 -> Symbol
  types 0F = CON
  types 1F = CON

  enter : Port 0 types -> Port 0 types 
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

      cycles-back : (x : Port 0 types) -> enter (enter x) ≡ x
      cycles-back (port 0F # 0F) = refl
      cycles-back (port 0F # 1F) = refl
      cycles-back (port 0F # 2F) = refl
      cycles-back (port 1F # 0F) = refl
      cycles-back (port 1F # 1F) = refl
      cycles-back (port 1F # 2F) = refl

      not-same : (x : Port 0 types) -> Not (enter x ≡ x)
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

  enter : Port 0 types -> Port 0 types
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

      cycles-back : (x : Port 0 types) -> enter (enter x) ≡ x      
      cycles-back (port 0F # 0F) = refl
      cycles-back (port 1F # 0F) = refl
      cycles-back (port 1F # 1F) = refl
      cycles-back (port 1F # 2F) = refl
      cycles-back (port 2F # 0F) = refl
      cycles-back (port 3F # 0F) = refl

      not-same : (x : Port 0 types) -> Not (enter x ≡ x)
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

free-injective : ∀ {freeLen len : Nat} {t : Fin len → Symbol} {i j : Fin freeLen} → _≡_ {A = Port {len} freeLen t} (free i) (free j) → i ≡ j
free-injective refl = refl

_≡ᶠ?_ : ∀ {n} → (a b : Fin n) → Dec (a ≡ b)
0F ≡ᶠ? 0F = yes refl
0F ≡ᶠ? fs b = no λ{()}
fs a ≡ᶠ? 0F = no λ{()}
fs a ≡ᶠ? fs b = map′ (cong fs) (λ{refl → refl}) (a ≡ᶠ? b)
                                                           
IsFree : ∀ {n k : Nat} {t} → Port {n} k t → Set
IsFree (free x) = Unit
IsFree (port x) = Empty

freePort-punchOut :
    ∀ {n k t}
    → (p p' : Port {n} (succ k) t)
    → {{IsFree p}}
    → {{IsFree p'}}
    → p ≢ p'
    → Port {n} k t
freePort-punchOut (free p) (free p') p≢p' = free (punchOut {_} {p} λ{p≡p' → p≢p' (cong free p≡p')})

-- takes an enter function and removes a free port(from old to new)
rewire² : ∀ {k len : Nat} {t : Fin len → Symbol} {old-port new-port : Fin (succ (succ k))}
  → (enter : Port (succ (succ k)) t → Port (succ (succ k)) t)
  → (wc : WellConnected enter)
  → old-port ≢ new-port -- gap in free ports
  → (Port k t → Port k t)
rewire² {k} {len} {t} {old} {new} f wc old≢new p =
  -- we'll be seeing where is this k+2 free port connected to in the original enter function
  let p' = to p
      p'≢old×new = to≢old×new p
      p'' = from p' p'≢old×new
  in p''
  where
  open WellConnected wc

  -- Example: p can be in the range
  -- 0 1 2 3
  -- After pushing the free wires 1 and 3, to get the original(succ k) free port
  -- 0 1 1+1 2+1 3+1     [insert 1]
  -- 0 1 2   3   4
  -- 0 1 2   3   3+1 4+1 [insert 3]
  -- 0 1 2   3   4   5
  -- or
  -- 0 1 2   2+1 3+1     [insert 3-1, because of inner punchOut]
  -- 0 1 2   3   4
  -- 0 1 1+1 2+1 3+1 4+1 [insert 1]
  -- 0 1 2   3   4   5
  to : Port {len} k t → Port {len} (succ (succ k)) t
  to (free x) = free (punchIn old (punchIn (punchOut old≢new) x))
  to (port x) = port x

  to≢old×new : ∀ (p : Port {len} k t) → (to p ≢ free old) × (to p ≢ free new)
  to≢old×new (port p) = (λ()) , λ()
  to≢old×new (free p) = (p≢old ∘ free-injective) , (p≢new ∘ free-injective) -- p≢old ∘ free-injective
    where
    p≢old : punchIn old (punchIn (punchOut old≢new) p) ≢ old
    p≢old = punchInᵢ≢i old (punchIn (punchOut old≢new) p)
    p≢new : punchIn old (punchIn (punchOut old≢new) p) ≢ new
    p≢new p≡new = {!   !} 
    -- punchIn old (punchIn (punchOut old≢new) p) ≢ new
    -- punchIn (punchOut old≢new) p ≢ punchOut old≢new
    
  -- Whatever was connected to the old, must connect to the new  
  --         -- After removing old(1) for new(4)
  --   0     --   0    --   0
  -- ┌ 1 ┐   -- ┌───┐  --   1 
  -- | 2 |   -- | 2 |  -- ┌ 2
  -- └ 3 |   -- └ 3 |  -- └ 3
  --   4 ┘   --   4 ┘  --   4
  --   5     --   5    --
  open ≡-Reasoning
  from : (p : Port (succ (succ k)) t) → (p ≢ free old) × (p ≢ free new) → Port k t
  from (free p) ( p≢old , p≢new ) with (f (free p)) in fp≡p'
  ... | port p' = port p'
  ... | free p'
        with old ≡ᶠ? p' | new ≡ᶠ? p' 
  ...     | yes old≡p' | yes new≡p' = absurd (old≢new (trans old≡p' (sym new≡p')))
  ...     | no  old≢p' | no  new≢p' = free (punchOut² (old≢p' ∘ sym) (new≢p' ∘ sym) old≢new)
  from (free p) ( p≢old , p≢new ) | free p' | yes old≡p' | no new≢p'
    with f (free new) in fnew≡new' -- go see what the new port is connected to
  ... | port new' = port new'
  ... | free new' = free (punchOut² new'≢new new'≢old (old≢new ∘ sym))
      where
      fnew≢new : f (free new) ≢ free new
      fnew≢new = not-same (free new)
      new'≢new : new' ≢ new
      new'≢new new'≡new = fnew≢new
        (begin
          f (free new)  ≡⟨ fnew≡new' ⟩
          free new'     ≡⟨ cong free new'≡new ⟩
          free new      ∎)
      new'≢old : new' ≢ old
      new'≢old new'≡old = injective (p≢new ∘ sym) (begin
        f (free new)    ≡⟨ fnew≡new' ⟩
        free new'       ≡⟨ cong free new'≡old  ⟩
        free old        ≡⟨ cong free old≡p' ⟩
        free p'         ≡⟨ sym fp≡p' ⟩
        f (free p)      ∎)
  -- TODO: this is exactly the same as the above case
  from (free p) ( p≢old , p≢new ) | free p' | no  old≢p' | yes new≡p'
    with f (free old) in fold≡old' -- go see what the old port is connected to
  ... | port old' = port old'
  ... | free old' = free (punchOut² old'≢new old'≢old (old≢new ∘ sym))
      where
      fold≢old : f (free old) ≢ free old
      fold≢old = not-same (free old)
      old'≢old : old' ≢ old
      old'≢old old'≡old = fold≢old
        (begin
          f (free old)  ≡⟨ fold≡old' ⟩
          free old'     ≡⟨ cong free old'≡old ⟩
          free old      ∎)
      old'≢new : old' ≢ new
      old'≢new old'≡new = injective (p≢old ∘ sym) (begin
        f (free old)    ≡⟨ fold≡old' ⟩
        free old'       ≡⟨ cong free old'≡new  ⟩
        free new        ≡⟨ cong free new≡p' ⟩
        free p'         ≡⟨ sym fp≡p' ⟩
        f (free p)      ∎)
  from (port p) _ = port p

  open ≡-Reasoning
  to∘from : ∀ x ≢ → to (from x ≢) ≡ x
  to∘from (free x) _ = {!   !}
  to∘from (port x) _ = refl

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

    break : Port {len + n} 0 types'' → Port {len} 0 types ⊎ Port {n} 0 types'
    break (port node # slot) with from node
    ... | inj₁ p = inj₁ (port p # slot)
    ... | inj₂ p = inj₂ (port p # slot)


    Port⊎ : Set
    Port⊎ = Port {len} freeLen types ⊎ Port {n} freeLen types'

    Port⊎⁰ : Set
    Port⊎⁰ = Port {len} 0 types ⊎ Port {n} 0 types'
      
    IsFreePort : Port⊎ → Set
    IsFreePort (inj₁ (free x)) = Unit
    IsFreePort (inj₁ (port x)) = Empty
    IsFreePort (inj₂ (free x)) = Unit
    IsFreePort (inj₂ (port x)) = Empty

    data All {A : Set} (P : A → Set) : List A → Set where
      []  : All P []
      _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

    data Any {A : Set} (P : A → Set) : List A → Set where
      here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
      there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

    infix 4 _∈_ _∉_

    _∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
    x ∈ xs = Any (x ≡_) xs

    _∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
    x ∉ xs = Not (x ∈ xs)

    lift-Port⊎⁰ : Port⊎⁰ → Port⊎
    lift-Port⊎⁰ (inj₁ (port x)) = inj₁ (port x)
    lift-Port⊎⁰ (inj₂ (port x)) = inj₂ (port x)
                                                 

    _≡ᵖ?_ : (a b : Port⊎) → Dec (a ≡ b)
    inj₁ (free x) ≡ᵖ? inj₁ (free x₁) = map′ (cong (inj₁ ∘ free)) (λ{refl → refl}) (x ≡ᶠ? x₁)
    inj₁ (free x) ≡ᵖ? inj₁ (port x₁) = no λ{()}
    inj₁ (port x) ≡ᵖ? inj₁ (free x₁) = no λ{()}
    inj₁ (port node # slot) ≡ᵖ? inj₁ (port node₁ # slot₁) with node ≡ᶠ? node₁
    ... | yes refl = map′ (cong ((inj₁ ∘ port_) ∘ (node #_))) (λ{refl → refl}) (slot ≡ᶠ? slot₁)
    ... | no ¬n≡n' = no λ{refl → ¬n≡n' refl}
    inj₁ x ≡ᵖ? inj₂ y = no λ{()}
    inj₂ y ≡ᵖ? inj₁ x = no λ{()}
    inj₂ (free x) ≡ᵖ? inj₂ (free x₁) = map′ (cong (inj₂ ∘ free)) (λ{refl → refl}) (x ≡ᶠ? x₁)
    inj₂ (free x) ≡ᵖ? inj₂ (port x₁) = no λ{()}
    inj₂ (port x) ≡ᵖ? inj₂ (free x₁) = no λ{()}
    inj₂ (port node # slot) ≡ᵖ? inj₂ (port node₁ # slot₁) with node ≡ᶠ? node₁
    ... | yes refl = map′ (cong ((inj₂ ∘ port_) ∘ (node #_))) (λ{refl → refl}) (slot ≡ᶠ? slot₁)
    ... | no ¬n≡n' = no λ{refl → ¬n≡n' refl}
                                                                       
    checkIn : (p : Port {len} freeLen types ⊎ Port {n} freeLen types') → (ps : List (Port {len} freeLen types ⊎ Port {n} freeLen types')) → Dec (p ∈ ps)
    checkIn p [] = no λ{()}
    checkIn p (x ∷ ps) with checkIn p ps
    ... | yes p = yes (there p)
    checkIn p (h ∷ ps) | no ¬p with p ≡ᵖ? h
    ... | yes p' = yes (here p')
    ... | no ¬p' = no λ{ (here refl) → ¬p' refl ; (there p') → ¬p p'}
                     
   --  enter⊎' :
    --   ∀ {ps : List Port⊎}
    --   → (p : Port⊎)
    --   → (walk : WalkPath (p ∷ ps))
    --   → WalkResult (p ∷ ps)
    -- enter⊎' = {!!}
    -- enter⊎' {ps} (inj₁ x) walk with enter x
    -- ... | free p with checkIn (inj₂ (free p)) ps
    -- ...           | yes a = cycle {!!} (inj₂ (free p)) a
    -- ...           | no b = enter⊎' (inj₂ (free p)) (step {!!} (inj₂ (free p)) b)
    -- enter⊎' {ps} (inj₁ x) walk | port p = end (inj₁ (port p))
    -- enter⊎' {ps} a b = {!!}
    -- enter⊎' {ps} (inj₂ y) walk with enter' y
    -- ... | free p with checkIn (inj₁ (free p)) ps
    -- ...           | yes a = cycle walk (inj₁ (free p)) a
    -- ...           | no b = enter⊎' (inj₁ (free p)) (step walk (inj₁ (free p)) b)
    -- enter⊎' {ps} (inj₂ x) walk | port p = end (inj₂ (port p))
    -- with enter' y
    -- ... | free p = {!!}
    -- ... | port p = end walk (inj₂ (port p))
    
    data WalkPath : (ps : List Port⊎) → Set where
      start : (p : Port⊎) → WalkPath (p ∷ [])
      step : ∀ {ps : List Port⊎} → WalkPath ps → (p : Port⊎) → p ∉ ps → WalkPath (p ∷ ps)
  
    data FreeWalkPath : (n : Nat) → Set where
      start : Fin freeLen → FreeWalkPath freeLen
      step : ∀ {n} → FreeWalkPath (succ n) → Fin n → FreeWalkPath n

    data WalkResult (start : Port⊎) : Set where
      end : Port⊎⁰ → WalkResult start
      cycle : IsFreePort start → WalkResult start

    -- OUTER-LEVEL
    -- - in: starting point
    -- - out: end used port, or finite path that includes starting point and which all ports were free
    enter⊎-outer :
      (start : Port⊎)
      → WalkResult start
    enter⊎-outer (inj₁ x) with enter x
    ... | port p = end (inj₁ (port p))
    enter⊎-outer (inj₁ (free x)) | free p = {!!}
    enter⊎-outer (inj₁ (port x)) | free p = {!!}
    enter⊎-outer (inj₂ y) = {!!}

    data EnterData (k : Nat) : Set where
      mk-enter-data :
        (curr : Port k types ⊎ Port k types')
        → (e  : Port k types  → Port k types)
        → (e' : Port k types' → Port k types')
        → (we  : WellConnected e)
        → (we' : WellConnected e')
        → EnterData k

    data EnterResult (k : Nat) : Set where
      found : Port⊎⁰ → EnterResult k
      not-found : Fin k → EnterData k → EnterResult k
  
    open ≡-Reasoning

    enter⊎-inner-pop :
      ∀ {k}
      → EnterData (succ (succ k))
      → EnterResult k
    enter⊎-inner-pop {k} (mk-enter-data (inj₁ x) e₁ e₂ we₁ we₂) with e₁ x
    ... | port p = found (inj₁ (port p))
    ... | free p with e₂ (free p)
    ...           | port p' = found (inj₂ (port p'))
    ...           | free p' = not-found new-free-portᶠ (mk-enter-data new-free-port e₁' e₂' we₁' {!!})
                    where
                    open WellConnected we₁ renaming (not-same to not-same₁)
                    e₁p≢p : e₁ (free p) ≢ free p
                    e₁p≢p = not-same₁ (free p)
                    p≢p' : p ≢ p'
                    p≢p' = {!!}
                    new-free-portᶠ : Fin k
                    new-free-portᶠ = {!!} -- punchOut p≢p'
                    new-free-port = inj₁ (free new-free-portᶠ)
                    e₁' = {!!} -- rewire¹ e₁ p≢p'
                    e₂' = {!!} -- rewire¹ e₂ p≢p'
                    we₁' : WellConnected e₁'
                    we₁' = record
                      { cycles-back = λ{x₁ → {!!}}
                      ; not-same = {!!} }
    enter⊎-inner-pop {k} x = {!!}

    -- RECURSIVE STEP(INNER PART)
    -- - in: 
    enter⊎-inner :
      ∀ {k}
      → (path : FreeWalkPath k)
      → EnterData k
      → Port 0 types ⊎ Port 0 types'
    enter⊎-inner {zero} (start ()) enter-data
    enter⊎-inner {zero} (step path ()) enter-data
    enter⊎-inner {succ zero} (start 0F) enter-data = {!!}
    enter⊎-inner {succ zero} (step path 0F) enter-data = {!!}
    enter⊎-inner {succ (succ k)} path enter-data with enter⊎-inner-pop enter-data
    ... | found p = p
    ... | not-found popped-free enter-data' = enter⊎-inner (step {!!} popped-free) enter-data'

    -- IDEA: have a data type that represents walking through the wires
    -- - cycle-free: there's a finite walk that ends up in a UsedPort
    -- - with cycle: there's a walk that consists of only FreePorts that cycle back a->b->c->d->a
    -- Proof Objective: if i start from a usedport i always end up in a usedport
 
    enter⊎ : Port⊎⁰ → Port⊎⁰
    enter⊎ (inj₁ (port x)) with enter⊎-outer (inj₁ (port x))
    ... | end e = e
    ... | cycle a = absurd a
    enter⊎ (inj₂ (port x)) with enter⊎-outer (inj₂ (port x))
    ... | end e = e
    ... | cycle a = absurd a

    ammend : Port {len} 0 types ⊎ Port {n} 0 types' → Port {len + n} 0 types''
    ammend (inj₁ (port node # slot)) =
      port
        to (inj₁ node) #
        subst (λ x → Fin (succ (arity x))) (sym (types''-to (inj₁ node))) slot
    ammend (inj₂ (port node # slot)) =
      port
        to (inj₂ node) #
        subst (λ x → Fin (succ (arity x))) (sym (types''-to (inj₂ node))) slot

    enter'' : Port {len + n} 0 types'' → Port {len + n} 0 types''
    enter'' p = ammend (enter⊎ (break p))

    well-connected'' : WellConnected enter''
    well-connected'' = {!!}

      


-- anni-rule : ∀ {len freeLen} → (g : Graph  (succ (succ len)) freeLen) → (ap : ActivePair {sA = ERA} {sB = ERA} g) → Graph len freeLen
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
                   
   