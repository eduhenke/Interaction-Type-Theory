module Base where

open import Agda.Builtin.Bool public
open import Agda.Builtin.Char public
open import Agda.Builtin.Equality public
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public renaming ( just to some ; nothing to none )
open import Agda.Builtin.Nat public renaming ( suc to succ ; _==_ to eq )
open import Agda.Builtin.String public
open import Agda.Builtin.Sigma public using ( Σ; _,_ )
open import Agda.Builtin.TrustMe public
open import Agda.Builtin.Unit public renaming ( ⊤ to Unit ; tt to unit )
open import Agda.Primitive public

data Empty : Set where

data Pair (a b : Set) : Set where
  pair : a -> b -> Pair a b

infixr 1 _⊎_

data _⊎_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_] : ∀ {c : Level} {A B : Set} {C : A ⊎ B → Set c} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

[_,_]′ : ∀ {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[_,_]′ = [_,_]

id : ∀ {A : Set} → A → A
id x = x

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} → (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

------------------------------------------------------------------------
-- Definition of non-dependent products

infixr 2 _×_

_×_ : ∀ {a b} → (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

------------------------------------------------------------------------
-- Existential quantifiers

∃ : ∀ {a b} → {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃₂ : ∀ {a b c} → {A : Set a} {B : A → Set b}
     (C : (x : A) → B x → Set c) → Set (a ⊔ b ⊔ c)
∃₂ C = ∃ λ a → ∃ λ b → C a b

-- Syntax

∃-syntax :  ∀ {a b} → {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B


data Fin : Nat -> Set where
  fz : ∀ {n} -> Fin (succ n)
  fs : ∀ {n} -> Fin n -> Fin (succ n)

Not : {a : Level} -> Set a -> Set a
Not a = a -> Empty

_≢_ : {a : Level} {A : Set a} -> A -> A -> Set a
x ≢ y = Not (x ≡ y)

if : ∀ {a : Set} -> Bool -> a -> a -> a
if true  t f = t
if false t f = f

may : ∀ {a b : Set} -> Maybe b -> (b -> a) -> a -> a
may (some x) s n = s x
may none     s n = n

pred : Nat -> Nat
pred zero     = zero
pred (succ x) = x

max : Nat -> Nat -> Nat
max zero     b        = b
max a        zero     = a
max (succ a) (succ b) = succ (max a b)

len : ∀ {a : Set} -> List a -> Nat
len []      = 0
len (x ∷ xs) = succ (len xs)

foldr : ∀ {a b : Set} -> (a -> b -> b) -> b -> List a -> b
foldr f z []      = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

mmap : ∀ {a b : Set} -> (a -> b) -> Maybe a -> Maybe b
mmap f none     = none
mmap f (some x) = some (f x)

when : ∀ {a b : Set} -> Maybe a -> (a -> b) -> b -> b
when none     s n = n
when (some x) s n = s x

Unwrap : ∀ {a : Set} -> Maybe a -> (a -> Set) -> Set
Unwrap none     f = Unit
Unwrap (some x) f = f x

sym : ∀ {a} {A : Set a} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans refl refl  =  refl


apl : ∀ {a b} {A : Set a} {B : Set b} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
apl f refl = refl

subst : ∀ {a} {A : Set a} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

IsSome : {a : Set} -> (x : Maybe a) -> Set
IsSome none     = Empty
IsSome (some x) = Unit

absurd : {a : Set} -> Empty -> a
absurd ()

-- decidable:
-- allows us to get the evidence or concrete result of a decidable procedure or both
data Dec (A : Set) : Set where
  yes :      A  -> Dec A
  no  : (Not A) -> Dec A

-- useful for allowing arguments that only respect a certain condition
-- more used for statically known values
-- ... -> {_ : T (decidable-procedure a b)} -> ...
T : Bool -> Set
T true = Unit
T false = Empty

erase : ∀ {A : Set} → Dec A → Bool
erase (yes x)  =  true
erase (no ¬x)  =  false

toWitness : ∀ {A : Set} {D : Dec A} → T (erase D) → A
toWitness {A} {yes x} unit  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T (erase D)
fromWitness {A} {yes x} _  =  unit
fromWitness {A} {no ¬x} x  =  ¬x x

map′ : ∀ {P Q : Set} → (P → Q) → (Q → P) → Dec P → Dec Q
map′ P→Q Q→P (yes p) = yes (P→Q p)
map′ P→Q Q→P (no ¬p) = no λ{q → ¬p (Q→P q)}

-- less-than-equal
infix 4 _<=_
data _<=_ : Nat -> Nat -> Set where
  z<=n : ∀ {n : Nat} -> zero <= n
  s<=s : ∀ {m n : Nat} -> m <= n -> succ m <= succ n



<=→<=s : ∀ {m n : Nat} → m <= n → m <= (succ n)
<=→<=s z<=n = z<=n
<=→<=s (s<=s m<=n) =
  let ind = <=→<=s m<=n
  in s<=s ind

¬s<=z : ∀ {m : Nat} → Not (succ m <= zero)
¬s<=z ()

¬s<=s : ∀ {m n : Nat} → Not (m <= n) → Not (succ m <= succ n)
¬s<=s ¬m<=n (s<=s m<=n) = ¬m<=n m<=n

¬s<=s' : ∀ {m n : Nat} → Not (succ m <= succ n) → Not (m <= n)
¬s<=s' ¬m<=n m<=n = ¬m<=n (s<=s m<=n)


¬<=-inv : ∀ {m n : Nat} → Not (m <= n) → (succ n <= m)
¬<=-inv {zero} {zero} ¬m<=n = absurd (¬m<=n z<=n)
¬<=-inv {zero} {succ n} ¬m<=n = absurd (¬m<=n (<=→<=s z<=n))
¬<=-inv {succ m} {zero} ¬m<=n = s<=s z<=n
¬<=-inv {succ m} {succ n} ¬m<=n = s<=s ind
  where
  ind = ¬<=-inv (¬s<=s' ¬m<=n)

_<=?_ : ∀ (m n : Nat) → Dec (m <= n)
zero  <=? n                   =  yes z<=n
succ m <=? zero                =  no ¬s<=z
succ m <=? succ n with m <=? n
...               | yes m<=n  =  yes (s<=s m<=n)
...               | no ¬m<=n  =  no (¬s<=s ¬m<=n)


-- allows to build any Fin n, if the values are statically known:
-- fn 50 : Fin 100
fn : ∀ {m : Nat} -> (n : Nat) -> {n<=m : T (erase ((succ n) <=? m))} -> Fin m
fn {m} n {n<=m} = fn' n (toWitness n<=m)
  where
  fn' : ∀ {m : Nat} -> (n : Nat) -> (succ n) <= m -> Fin m
  fn' {succ m} zero n<=m = fz
  fn' {succ m} (succ n) (s<=s n<=m) = fs (fn' n n<=m)

-- useful in pattern matching of Fin
pattern 0F = fz
pattern 1F = fs 0F
pattern 2F = fs 1F
pattern 3F = fs 2F
pattern 4F = fs 3F
pattern 5F = fs 4F
pattern 6F = fs 5F
pattern 7F = fs 6F
pattern 8F = fs 7F
pattern 9F = fs 8F

toNat : ∀ {n} → Fin n → Nat
toNat fz    = zero
toNat (fs i) = succ (toNat i)

fromNat<= : {m n : Nat} → (succ m) <= n → Fin n
fromNat<= {zero} (s<=s z<=n) = fz
fromNat<= {succ m} {succ n} (s<=s m<=n) = fs (fromNat<= m<=n)


toNat⁻¹ : ∀ {n : Nat} {f : Fin n} → Fin (toNat f) → Fin n
toNat⁻¹ {succ n} {f} f' = f

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl


↑ : ∀ {m} → Fin m → Fin (succ m)
↑ fz = fz
↑ (fs i) = fs (↑ i)


fpred : ∀ {n} → Fin n → Fin n
fpred fz = fz
fpred (fs f) = ↑ f

lower₁ : ∀ {n : Nat} → (i : Fin (succ n)) → n ≢ toNat i → Fin n
lower₁ {zero}  fz    ne = absurd (ne refl)
lower₁ {succ n} fz    _  = fz
lower₁ {succ n} (fs i) ne = fs (lower₁ i (ne ∘ cong succ))

-- The function f(i,j) = if j>i then j-1 else j
-- This is a variant of the thick function from Conor
-- McBride's "First-order unification by structural recursion".
punchOut : ∀ {n : Nat} {i j : Fin (succ n)} → i ≢ j → Fin n
punchOut {_}     {fz}     {fz}  i≢j = absurd (i≢j refl)
punchOut {_}     {fz}     {fs j} _   = j
punchOut {succ _} {fs i}   {fz}  _   = fz
punchOut {succ _} {fs i}   {fs j} i≢j = fs (punchOut (i≢j ∘ cong fs))

punchOut² : ∀ {n : Nat} {i j k : Fin (succ (succ n))} → (i ≢ j) → (i ≢ k) → (j ≢ k) → Fin n
punchOut² {n} {0F} {0F} {_} i≢j i≢k j≢k = absurd (i≢j refl)
punchOut² {n} {0F} {_} {0F} i≢j i≢k j≢k = absurd (i≢k refl)
punchOut² {zero} {0F} {1F} {1F} i≢j i≢k j≢k = absurd (j≢k refl)
punchOut² {succ n} {0F} {fs j} {fs k} i≢j i≢k j≢k = 0F
punchOut² {n} {_} {0F} {0F} i≢j i≢k j≢k = absurd (j≢k refl)
punchOut² {zero} {1F} {0F} {1F} i≢j i≢k j≢k = absurd (i≢k refl)
punchOut² {succ n} {fs i} {0F} {fs k} i≢j i≢k j≢k = punchOut (i≢k ∘ (sym ∘ cong fs))
punchOut² {zero} {1F} {1F} {0F} i≢j i≢k j≢k = absurd (i≢j refl)
punchOut² {succ n} {fs i} {fs j} {0F} i≢j i≢k j≢k = punchOut (i≢j ∘ (sym ∘ cong fs))
punchOut² {zero} {_} {1F} {1F} i≢j i≢k j≢k = absurd (j≢k refl)
punchOut² {succ n} {fs i} {fs j} {fs k} i≢j i≢k j≢k = fs (punchOut² (i≢j ∘ cong fs) (i≢k ∘ cong fs) (j≢k ∘ cong fs))

-- The function f(i,j) = if j≥i then j+1 else j
punchIn : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
punchIn fz    j       = fs j
punchIn (fs i) fz     = fz
punchIn (fs i) (fs j) = fs (punchIn i j)


punchIn-punchOut : ∀ {n} {i j : Fin (succ n)} (i≢j : i ≢ j) →
                   punchIn i (punchOut i≢j) ≡ j
punchIn-punchOut {_}     {fz}   {fz}  0≢0 = absurd (0≢0 refl)
punchIn-punchOut {_}     {fz}   {fs j} _   = refl
punchIn-punchOut {succ m} {fs i}  {fz}  i≢j = refl
punchIn-punchOut {succ m} {fs i}  {fs j} i≢j =
  cong fs (punchIn-punchOut (i≢j ∘ cong fs))

suc-injective : ∀ {n} {i j : Fin n} → fs i ≡ fs j → i ≡ j
suc-injective refl = refl

punchIn-injective : ∀ {n} i (j k : Fin n) →
                    punchIn i j ≡ punchIn i k → j ≡ k
punchIn-injective fz     _      _      refl      = refl
punchIn-injective (fs i) fz     fz     _         = refl
punchIn-injective (fs i) (fs j) (fs k) ↑j+1≡↑k+1 =
  cong fs (punchIn-injective i j k (suc-injective ↑j+1≡↑k+1))

punchInᵢ≢i : ∀ {n} i (j : Fin n) → punchIn i j ≢ i
punchInᵢ≢i (fs i) (fs j) = punchInᵢ≢i i j ∘ suc-injective


-- canonical liftings of i:Fin m to larger index

-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m + n)
fz    ↑ˡ n = fz
(fs i) ↑ˡ n = fs (i ↑ˡ n)

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n + m)
zero    ↑ʳ i = i
(succ n) ↑ʳ i = fs (n ↑ʳ i)

Sum-map : ∀ {A B C D : Set} → (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
Sum-map f g = [ inj₁ ∘ f , inj₂ ∘ g ]′


module ≡-Reasoning {a : Level} {A : Set a} where

  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = trans x≡y y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z



-- splitAt m "i" = inj₁ "i"      if i < m
--                 inj₂ "i - m"  if i ≥ m
-- This is dual to splitAt from Data.Vec.

splitAt : ∀ {m n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt {zero}    i      = inj₂ i
splitAt {succ m} fz    = inj₁ fz
splitAt {succ m} (fs i) = Sum-map fs id (splitAt {m} i)

-- inverse of above function
join : ∀ {m n} → Fin m ⊎ Fin n → Fin (m + n)
join {m} {n} = [ _↑ˡ n , m ↑ʳ_ ]′

------------------------------------------------------------------------
-- splitAt
------------------------------------------------------------------------

-- Fin (m + n) ↔ Fin m ⊎ Fin n

splitAt-↑ˡ : ∀ m i n → splitAt {m} (i ↑ˡ n) ≡ inj₁ i
splitAt-↑ˡ (succ m) fz    n = refl
splitAt-↑ˡ (succ m) (fs i) n rewrite splitAt-↑ˡ m i n = refl

splitAt⁻¹-↑ˡ : ∀ {m} {n} {i} {j} → splitAt {m} {n} i ≡ inj₁ j → j ↑ˡ n ≡ i
splitAt⁻¹-↑ˡ {succ m} {n} {0F} {.0F} refl = refl
splitAt⁻¹-↑ˡ {succ m} {n} {fs i} {j} eq with splitAt {m} i in splitAt[m][i]≡inj₁[j]
... | inj₁ k with refl ← eq = cong fs (splitAt⁻¹-↑ˡ {i = i} {j = k} splitAt[m][i]≡inj₁[j])

splitAt-↑ʳ : ∀ m n i → splitAt {m} (m ↑ʳ i) ≡ inj₂ {B = Fin n} i
splitAt-↑ʳ zero    n i = refl
splitAt-↑ʳ (succ m) n i rewrite splitAt-↑ʳ m n i = refl

splitAt⁻¹-↑ʳ : ∀ {m} {n} {i} {j} → splitAt {m} {n} i ≡ inj₂ j → m ↑ʳ j ≡ i
splitAt⁻¹-↑ʳ {zero}  {n} {i} {j} refl = refl
splitAt⁻¹-↑ʳ {succ m} {n} {fs i} {j} eq with splitAt {m} i in splitAt[m][i]≡inj₂[k]
... | inj₂ k with refl ← eq = cong fs (splitAt⁻¹-↑ʳ {i = i} {j = k} splitAt[m][i]≡inj₂[k])

splitAt-join : ∀ m n i → splitAt {m} (join {m} {n} i) ≡ i
splitAt-join m n (inj₁ x) = splitAt-↑ˡ m x n
splitAt-join m n (inj₂ y) = splitAt-↑ʳ m n y


postulate
  -- TODO: would need to import a lot of stuff from std
  join-splitAt : ∀ m n i → join {m} {n} (splitAt {m} i) ≡ i

-- join-splitAt zero    n i       = refl
-- join-splitAt (succ m) n zero    = refl
-- join-splitAt (succ m) n (succ i) = begin
--   [ _↑ˡ n , (succ m) ↑ʳ_ ]′ (splitAt (succ m) (fs i)) ≡⟨ [,]-map (splitAt m i) ⟩
--   [ fs ∘ (_↑ˡ n) , fs ∘ (m ↑ʳ_) ]′ (splitAt m i)   ≡˘⟨ [,]-∘ suc (splitAt m i) ⟩
--   fs ([ _↑ˡ n , m ↑ʳ_ ]′ (splitAt m i))             ≡⟨ cong fs (join-splitAt m n i) ⟩
--   fs i                                                         ∎
--   where open ≡-Reasoning


-- Well Founded Stuff

data Acc {A : Set} (R : A -> A -> Set) (x : A) : Set where
  acc : (p : ∀ y -> R y x -> Acc R y) -> Acc R x

WF : {A : Set} (R : A -> A -> Set) -> Set
WF R = ∀ x -> Acc R x

data _<N_ : Nat -> Nat -> Set where
  <base : ∀ {a} -> a <N succ a
  <step : ∀ {a b} -> a <N b -> a <N succ b

WF< : WF _<N_ 
WF< zero     = acc (λ y ())
WF< (succ x) = acc (λ y f -> aux x y f) where
  aux : (x y : Nat) -> y <N succ x -> Acc _<N_ y
  aux x .x <base = WF< x
  aux x  y (<step f) with WF< x
  ... | acc p = p y f
