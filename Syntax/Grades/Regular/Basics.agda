------------------------------------------------------------------------
-- Shared lemmas: Boolean tests, lists by position, and the ranges of --
-- table states.                                                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; _≡ᵇ_; z≤n; s≤s)

module Syntax.Grades.Regular.Basics (k : ℕ) where

open import Data.Bool.Base using (Bool; true; false; T; not; _∧_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import Syntax.Grades.Regular.Automaton k

------------------------------------------------------------------------
-- Booleans

T-true : ∀ {b} → b ≡ true → T b
T-true refl = tt

T-false : ∀ {b} → b ≡ false → ¬ T b
T-false refl ()

-- Booleans true together are equal

T-ext : ∀ {a b : Bool} → (T a → T b) → (T b → T a) → a ≡ b
T-ext {false} {false} f g = refl
T-ext {false} {true}  f g with g tt
... | ()
T-ext {true}  {false} f g with f tt
... | ()
T-ext {true}  {true}  f g = refl

T-∧⁻ : ∀ {a b} → T (a ∧ b) → T a × T b
T-∧⁻ {true} {true} _ = tt , tt

T-∧⁺ : ∀ {a b} → T a → T b → T (a ∧ b)
T-∧⁺ {true} {true} _ _ = tt

T-not⁻ : ∀ {b} → T (not b) → ¬ T b
T-not⁻ {false} _ ()

T-not⁺ : ∀ {b} → ¬ T b → T (not b)
T-not⁺ {false} _ = tt
T-not⁺ {true}  n = n tt

T-if : ∀ {A : Set} b {x y : A} → T b → (if b then x else y) ≡ x
T-if true _ = refl

F-if : ∀ {A : Set} b {x y : A} → ¬ T b → (if b then x else y) ≡ y
F-if false _ = refl
F-if true  n = ⊥-elim (n tt)

if-case : ∀ {A : Set} (P : A → Set) b {x y : A}
        → (b ≡ true → P x) → (b ≡ false → P y) → P (if b then x else y)
if-case P true  t f = t refl
if-case P false t f = f refl

T-subst : ∀ {a b : Bool} → a ≡ b → T a ⇔ T b
T-subst refl = mk⇔ (λ t → t) (λ t → t)

_∘⇔_ : ∀ {A B C : Set} → B ⇔ C → A ⇔ B → A ⇔ C
g ∘⇔ f = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
             (λ c → Equivalence.from f (Equivalence.from g c))

-- numbers and lists of numbers

≡ᵇ-refl : ∀ n → T (n ≡ᵇ n)
≡ᵇ-refl n = ≡⇒≡ᵇ n n refl

≡ᵇ-true : ∀ {m n} → (m ≡ᵇ n) ≡ true → m ≡ n
≡ᵇ-true {m} {n} e = ≡ᵇ⇒≡ m n (T-true e)

≡ᵇ-false : ∀ {m n} → (m ≡ᵇ n) ≡ false → m ≢ n
≡ᵇ-false {m} {n} e m≡n = T-false e (≡⇒≡ᵇ m n m≡n)

==ⁿ-sound : ∀ xs ys → T (xs ==ⁿ ys) → xs ≡ ys
==ⁿ-sound []       []       _ = refl
==ⁿ-sound (x ∷ xs) (y ∷ ys) h =
  cong₂ _∷_ (≡ᵇ⇒≡ x y (proj₁ (T-∧⁻ h))) (==ⁿ-sound xs ys (proj₂ (T-∧⁻ h)))

==ⁿ-refl : ∀ xs → T (xs ==ⁿ xs)
==ⁿ-refl []       = tt
==ⁿ-refl (x ∷ xs) = T-∧⁺ (≡ᵇ-refl x) (==ⁿ-refl xs)

------------------------------------------------------------------------
-- Lists by position

module _ {A : Set} where

  ‼-++ : (xs ys : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → (xs ++ ys) ‼ i ≡ just x
  ‼-++ []       ys {i}     ()
  ‼-++ (x ∷ xs) ys {zero}  refl = refl
  ‼-++ (x ∷ xs) ys {suc i} eq   = ‼-++ xs ys eq

  ‼-at : (xs : List A) {y : A} {ys : List A} → (xs ++ y ∷ ys) ‼ length xs ≡ just y
  ‼-at []       = refl
  ‼-at (x ∷ xs) = ‼-at xs

  ‼-< : (xs : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → i < length xs
  ‼-< []       {i}     ()
  ‼-< (x ∷ xs) {zero}  refl = s≤s z≤n
  ‼-< (x ∷ xs) {suc i} eq   = s≤s (‼-< xs eq)

  ‼-≥ : (xs : List A) {i : ℕ} → length xs ≤ i → xs ‼ i ≡ nothing
  ‼-≥ []       _         = refl
  ‼-≥ (x ∷ xs) (s≤s le) = ‼-≥ xs le

  ‼-nothing : (xs : List A) {i : ℕ} → xs ‼ i ≡ nothing → length xs ≤ i
  ‼-nothing []       _         = z≤n
  ‼-nothing (x ∷ xs) {zero}  ()
  ‼-nothing (x ∷ xs) {suc i} eq = s≤s (‼-nothing xs eq)

  ‼-exists : (xs : List A) {i : ℕ} → i < length xs → ∃ λ x → xs ‼ i ≡ just x
  ‼-exists (x ∷ xs) {zero}  _         = x , refl
  ‼-exists (x ∷ xs) {suc i} (s≤s lt) = ‼-exists xs lt

  ‼-snoc : (xs : List A) {y : A} {i : ℕ} {x : A}
         → (xs ++ y ∷ []) ‼ i ≡ just x → xs ‼ i ≡ just x ⊎ (i ≡ length xs × x ≡ y)
  ‼-snoc []       {i = zero}  refl = inj₂ (refl , refl)
  ‼-snoc []       {i = suc i} ()
  ‼-snoc (x ∷ xs) {i = zero}  refl = inj₁ refl
  ‼-snoc (x ∷ xs) {i = suc i} eq with ‼-snoc xs eq
  ... | inj₁ eq′         = inj₁ eq′
  ... | inj₂ (refl , e) = inj₂ (refl , e)

  ‼-All : {P : A → Set} {xs : List A} {i : ℕ} {x : A} → All P xs → xs ‼ i ≡ just x → P x
  ‼-All {xs = x ∷ xs} {zero}  (px ∷ _)   refl = px
  ‼-All {xs = x ∷ xs} {suc i} (_  ∷ pxs) eq   = ‼-All pxs eq

  All-‼ : {P : A → Set} (xs : List A) → (∀ {i x} → xs ‼ i ≡ just x → P x) → All P xs
  All-‼ []       h = []
  All-‼ (x ∷ xs) h = h {zero} refl ∷ All-‼ xs (λ {i} → h {suc i})

  ‼-Any : {P : A → Set} (xs : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → P x → Any P xs
  ‼-Any (x ∷ xs) {zero}  refl px = here px
  ‼-Any (x ∷ xs) {suc i} eq   px = there (‼-Any xs eq px)

  lookupOr-‼ : {d : A} (xs : List A) {i : ℕ} {x : A} → xs ‼ i ≡ just x → lookupOr d xs i ≡ x
  lookupOr-‼ (x ∷ xs) {zero}  refl = refl
  lookupOr-‼ (x ∷ xs) {suc i} eq   = lookupOr-‼ xs eq

  ‼-map : {B : Set} (f : A → B) (xs : List A) {i : ℕ} {x : A}
        → xs ‼ i ≡ just x → map f xs ‼ i ≡ just (f x)
  ‼-map f (x ∷ xs) {zero}  refl = refl
  ‼-map f (x ∷ xs) {suc i} eq   = ‼-map f xs eq

  just-injective : {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

-- a total lookup inside the list

all-lookup : ∀ {A : Set} {P : A → Set} {d : A} {xs} {i}
           → All P xs → i < length xs → P (lookupOr d xs i)
all-lookup {i = zero}  (px ∷ _)   _         = px
all-lookup {i = suc i} (_ ∷ pxs)  (s≤s lt) = all-lookup pxs lt

------------------------------------------------------------------------
-- Tables

module _ (D : DFA) (wf : WellFormed D) where

  -- a successor of a state stays among the states

  next-< : ∀ {p} → p < size D → ∀ a → next D p a < size D
  next-< p< a with all-lookup {d = []} (proj₂ (proj₂ wf)) p<
  ... | len , targets = all-lookup targets (subst (toℕ a <_) (sym len) (toℕ<n a))

  run-< : ∀ {p} w → p < size D → run D p w < size D
  run-< []      lt = lt
  run-< (a ∷ w) lt = run-< w (next-< lt a)

  start-< : 0 < size D
  start-< = proj₁ wf

run-++ : ∀ D p u v → run D p (u ++ v) ≡ run D (run D p u) v
run-++ D p []      v = refl
run-++ D p (a ∷ u) v = run-++ D (next D p a) u v

-- the transitions of a table's automaton are the table's

δ*-table : ∀ D p w → Automaton.δ* (automaton D) p w ≡ run D p w
δ*-table D p []      = refl
δ*-table D p (a ∷ w) = δ*-table D (next D p a) w
