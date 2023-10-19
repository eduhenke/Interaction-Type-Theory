open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

data Net : ℕ → ℕ → Set where
  empty : Net 0 0
  ε⁺ : Net 0 1
  ε⁻ : Net 1 0
  δ⁺ : Net 2 1
  δ⁻ : Net 1 2
  γ⁺ : Net 2 1
  γ⁻ : Net 1 2
  id : ∀ {i} → Net i i
  _⊕_ : ∀ {i₁ i₂ o₁ o₂ i o : ℕ} → {{i ≡ i₁ + i₂}} → {{o ≡ o₁ + o₂}}
    → Net i₁ o₁
    → Net i₂ o₂
    ------------
    → Net i o
  _;_ : ∀ {i o k : ℕ}
    → Net i k
    → Net   k o
    → Net i   o


reduce : ∀ {i o} → Net i o → Net i o
reduce (ε⁺ ; ε⁻) = empty
reduce (ε⁺ ; δ⁻) = ε⁺ ⊕ ε⁺
reduce (ε⁺ ; γ⁻) = ε⁺ ⊕ ε⁺
reduce (ε⁺ ; id) = ε⁺
reduce {o = zero} (ε⁺ ; _⊕_ {zero} {suc i2} {.0} {zero} {.1} {.zero} ⦃ ieq ⦄ ⦃ oeq ⦄ empty n₂) = empty
reduce (ε⁺ ; _⊕_ {suc i1} {i2} {o1} {o2} {.1} {o} ⦃ ieq ⦄ ⦃ oeq ⦄ n₁ n₂) = {!   !}
reduce (ε⁺ ; (n₁ ; n₂)) = {!   !} -- (reduce (ε⁺ ; n₁)) ; n₂
reduce (ε⁻ ; n₁) = {!   !}
reduce (δ⁺ ; n₁) = {!   !}
reduce (δ⁻ ; n₁) = {!   !}
reduce (γ⁺ ; n₁) = {!   !}
reduce (γ⁻ ; n₁) = {!   !}
reduce (id ; n₁) = reduce n₁
reduce net = net