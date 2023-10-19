open import Data.Maybe
open import Data.Product
open import Data.List
open import Data.Fin 
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong-app)
open import Data.Nat using (ℕ; zero; suc; _+_)


data Symbol : Set₀ where
  ERA : Symbol
  CON : Symbol
  DUP : Symbol

arity : Symbol → ℕ
arity ERA = 1
arity _ = 3


infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

IsFinite : Set → Set
IsFinite A = ∀ {n} → A ≃ Fin n



-- a : A
-- let f  : Fin (n + 1) = to a
-- let f' : Fin n       = punchout f
-- let a' = from f' -- err

-- A' ≤ A

-- A' = ∀ (a : Nat) → (a ≢ 3)

record Net : Set₁ where
  field
    Free : Set
    Node : Set

    -- types
    l : Node → Symbol
    
  NodePort = Σ[ c ∈ Node ] Fin (arity (l c))
  Port = NodePort ⊎ Free

  field
    partnerOf : Port → Port
    wellConnected : (∀ x → partnerOf x ≢ x) × (∀ x → partnerOf (partnerOf x) ≡ x)

    FinFree : IsFinite Free
    FinNode : IsFinite Node
    -- FinW : IsFinite W


overlayNets : Net -> Net -> Net
overlayNets a b = record
  { Free = Free'
  ; Node = Node'
  ; l = l'
  ; partnerOf = {!   !}
  ; wellConnected = {!   !}
  ; FinFree = FinFree'
  ; FinNode = FinNode'
  }
  where
    Free' = (Net.Free a) ⊎ (Net.Free b)
    Node' = (Net.Node a) ⊎ (Net.Node b)

    l' : Node' → Symbol
    l' = [ Net.l a , Net.l b ]′

    FinFree' : IsFinite Free'
    FinFree' = {!   !}

    FinNode' : IsFinite Node'
    FinNode' = {!   !}
      -- record
      -- { to = λ{x → [ _≃_.to (Net.FinFree a) , _≃_.to (Net.FinFree b) ]′ x}
      -- ; from = λ{x → {!   !}}
      -- ; from∘to = {!   !}
      -- ; to∘from = {!   !} }
    

    -- (fst ∈ Node, slot ∈ arity)
    NodePort' = Σ[ c ∈ Node' ] Fin (arity (l' c))
    Port' = NodePort' ⊎ Free'



    partnerOf' : Port' → Port'
    partnerOf' (inj₁ (inj₁ x , snd)) = {!   !}
      where
        open Net a
        xPartner = Net.partnerOf a (inj₁ (x , snd))
        
    partnerOf' (inj₁ (inj₂ y , snd)) = {!   !}
    partnerOf' (inj₂ y) = {!   !}

