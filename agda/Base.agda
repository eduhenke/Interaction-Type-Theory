module Base where

open import Agda.Builtin.Bool public
open import Agda.Builtin.Char public
open import Agda.Builtin.Equality public renaming ( _≡_ to _==_ )
open import Agda.Builtin.List public renaming ( [] to nil ; _∷_ to _#_ )
open import Agda.Builtin.Maybe public renaming ( just to some ; nothing to none )
open import Agda.Builtin.Nat public renaming ( suc to succ ; _==_ to eq )
open import Agda.Builtin.String public
open import Agda.Builtin.Sigma public renaming ( Σ to S )
open import Agda.Builtin.TrustMe public
open import Agda.Builtin.Unit public renaming ( ⊤ to Unit ; tt to unit )
open import Agda.Primitive public

data Empty : Set where

data Pair (a b : Set) : Set where
  pair : a -> b -> Pair a b

data Fin : Nat -> Set where
  fz : ∀ {n} -> Fin (succ n)
  fs : ∀ {n} -> Fin n -> Fin (succ n)

Not : {a : Level} -> Set a -> Set a
Not a = a -> Empty

_!=_ : {a : Level} {A : Set a} -> A -> A -> Set a
x != y = Not (x == y)

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
len nil      = 0
len (x # xs) = succ (len xs)

foldr : ∀ {a b : Set} -> (a -> b -> b) -> b -> List a -> b
foldr f z nil      = z
foldr f z (x # xs) = f x (foldr f z xs)

mmap : ∀ {a b : Set} -> (a -> b) -> Maybe a -> Maybe b
mmap f none     = none
mmap f (some x) = some (f x)

when : ∀ {a b : Set} -> Maybe a -> (a -> b) -> b -> b
when none     s n = n
when (some x) s n = s x

Unwrap : ∀ {a : Set} -> Maybe a -> (a -> Set) -> Set
Unwrap none     f = Unit
Unwrap (some x) f = f x

sym : ∀ {a} {A : Set a} {x y : A} -> x == y -> y == x
sym refl = refl

apl : ∀ {a b} {A : Set a} {B : Set b} (f : A -> B) {x y : A} -> x == y -> f x == f y
apl f refl = refl

rwt : ∀ {a} {A : Set a} {P : A → Set} {x y : A} -> x == y -> P x -> P y
rwt refl px = px

IsSome : {a : Set} -> (x : Maybe a) -> Set
IsSome none     = Empty
IsSome (some x) = Unit

absurd : {a : Set} -> Empty -> a
absurd ()

foo : ∀ x y -> succ x != succ y -> x != y
foo x y nsxy xy = nsxy (apl succ xy)

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

-- less-than-equal
infix 4 _<=_
data _<=_ : Nat -> Nat -> Set where
  z<=n : ∀ {n : Nat} -> zero <= n
  s<=s : ∀ {m n : Nat} -> m <= n -> succ m <= succ n

¬s<=z : ∀ {m : Nat} → Not (succ m <= zero)
¬s<=z ()

¬s<=s : ∀ {m n : Nat} → Not (m <= n) → Not (succ m <= succ n)
¬s<=s ¬m<=n (s<=s m<=n) = ¬m<=n m<=n

_<=?_ : ∀ (m n : Nat) → Dec (m <= n)
zero  <=? n                   =  yes z<=n
succ m <=? zero                =  no ¬s<=z
succ m <=? succ n with m <=? n
...               | yes m<=n  =  yes (s<=s m<=n)
...               | no ¬m<=n  =  no (¬s<=s ¬m<=n)


-- allows to build any Fin n, if the values are statically known:
-- fn 50 : Fin 100
fn : ∀ {m : Nat} -> (n : Nat) -> {n<=m : T (erase ((succ n) <=? m))} -> Fin m
fn {m} n {n<=m} = fn' n {toWitness n<=m}
  where
  fn' : ∀ {m : Nat} -> (n : Nat) -> {n<=m : (succ n) <= m} -> Fin m
  fn' {succ m} zero {n<=m} = fz
  fn' {succ m} (succ n) {s<=s n<=m} = fs (fn' n {n<=m})

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

