------------------------------------------------------------------------
-- Non-empty regular languages as a grade.                             --
--                                                                     --
-- A grade is a non-empty regular language over `Fin k`, held as its   --
-- canonical table, so equal languages are equal grades. The order is  --
-- inclusion, the product concatenation, the join union; `⊤` is every  --
-- word, `u` the empty word alone, and `of-nat n` the word `tickⁿ`.    --
--                                                                     --
-- Proofs about the tables of operations go through `subst` along word --
-- equations: comparing two such tables by computation unfolds their   --
-- symbolic exploration.                                               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin)

module Syntax.Grades.Regular.Grade (k : ℕ) (tick : Fin k) where

open import Data.Bool.Base using (Bool; true; false; T; _∨_)
open import Data.Bool.Properties using (T-∨; T-irrelevant)
open import Data.List.Base using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ++-conicalˡ; ++-conicalʳ)
open import Function.Base using (case_of_)
open import Data.Maybe.Base using (nothing)
open import Data.Product.Base using (_×_; _,_; ∃; ∃₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (T?; recompute)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Regular.Automaton k
open import Syntax.Grades.Regular.Canonical k
open import Syntax.Grades.Regular.Operations k
open import Syntax.Grades.Regular.Inclusion k
open import Syntax.Grades.Regular.Canonicity k using (canonicity; T-≡)
open import Syntax.Grades.Regular.Decide k
  using (⊆ᵇ-sound; ⊆ᵇ-complete; nonempty?; wellFormed?; _≟ᴰ_)
open import Syntax.Grades.Regular.Properties k

open Equivalence using (to; from)

------------------------------------------------------------------------
-- The carrier

record Regular : Set where
  constructor regular
  field
    table      : DFA
    .wf        : WellFormed table
    .canonical : canon table ≡ table
    .inhabited : ∃ λ w → w ∈ table

open Regular public using (table)

-- the side conditions, recomputed

wf′ : (c : Regular) → WellFormed (table c)
wf′ (regular t w _ _) = recompute (wellFormed? t) w

canonical′ : (c : Regular) → canon (table c) ≡ table c
canonical′ (regular t _ e _) = recompute (canon t ≟ᴰ t) e

inhabited′ : (c : Regular) → ∃ λ w → w ∈ table c
inhabited′ c@(regular t _ _ i) = recompute (nonempty? t (wf′ c)) i

table-injective : ∀ {c d} → table c ≡ table d → c ≡ d
table-injective {regular t _ _ _} {regular .t _ _ _} refl = refl

-- grades with the same language are equal

same-language : ∀ c d → (∀ w → w ∈ table c → w ∈ table d) → (∀ w → w ∈ table d → w ∈ table c)
              → c ≡ d
same-language c d cd dc =
  table-injective
    (trans (sym (canonical′ c))
      (trans (canonicity (table c) (table d) (wf′ c) (wf′ d) (λ w → T-≡ (cd w) (dc w)))
             (canonical′ d)))

------------------------------------------------------------------------
-- Operations

-- a single word

⟪_⟫ : Word → Regular
⟪ w ⟫ = regular ⟦ w ⟧ (⟦⟧-wf w) (⟦⟧-canonical w) (w , from (∈-⟦⟧ w w) refl)

u : Regular
u = ⟪ [] ⟫

⊤ : Regular
⊤ = regular Σ* Σ*-wf Σ*-canonical ([] , ∈-Σ* [])

of-nat : ℕ → Regular
of-nat n = ⟪ replicate n tick ⟫

_·ᴿ_ : Regular → Regular → Regular
c ·ᴿ d = regular (table c · table d) (·-wf {table c} {table d} (wf′ c) (wf′ d)) (·-canonical {table c} {table d} (wf′ c) (wf′ d)) inh
  where
  inh : ∃ λ w → w ∈ (table c · table d)
  inh with inhabited′ c | inhabited′ d
  ... | x , x∈ | y , y∈ = x ++ y , from (∈-· {table c} {table d} (wf′ c) (wf′ d) (x ++ y)) (x , y , refl , x∈ , y∈)

_⊔ᴿ_ : Regular → Regular → Regular
c ⊔ᴿ d = regular (table c ∪ table d) (∪-wf {table c} {table d} (wf′ c) (wf′ d)) (∪-canonical {table c} {table d} (wf′ c) (wf′ d)) inh
  where
  inh : ∃ λ w → w ∈ (table c ∪ table d)
  inh with inhabited′ c
  ... | x , x∈ = x , subst T (sym (∪-accepts {table c} {table d} (wf′ c) (wf′ d) x)) (from T-∨ (inj₁ x∈))

_≾_ : Regular → Regular → Set
c ≾ d = T (table c ⊆ᵇ table d)

infixl 7 _·ᴿ_
infixl 6 _⊔ᴿ_
infix  4 _≾_

------------------------------------------------------------------------
-- Languages of the operations

∈⟪⟫⁻ : ∀ v w → w ∈ table ⟪ v ⟫ → w ≡ v
∈⟪⟫⁻ v w = to (∈-⟦⟧ v w)

∈⟪⟫⁺ : ∀ v → v ∈ table ⟪ v ⟫
∈⟪⟫⁺ v = from (∈-⟦⟧ v v) refl

≾⇒⊆ : ∀ c d → c ≾ d → table c ⊆ table d
≾⇒⊆ c d = ⊆ᵇ-sound {table c} {table d} (wf′ c) (wf′ d)

⊆⇒≾ : ∀ c d → table c ⊆ table d → c ≾ d
⊆⇒≾ c d = ⊆ᵇ-complete {table c} {table d} (wf′ c) (wf′ d)

∈·⁺ : ∀ c d x y → x ∈ table c → y ∈ table d → (x ++ y) ∈ table (c ·ᴿ d)
∈·⁺ c d x y x∈ y∈ = from (∈-· {table c} {table d} (wf′ c) (wf′ d) (x ++ y)) (x , y , refl , x∈ , y∈)

∈·⁻ : ∀ c d w → w ∈ table (c ·ᴿ d) → ∃₂ λ x y → w ≡ x ++ y × x ∈ table c × y ∈ table d
∈·⁻ c d w = to (∈-· {table c} {table d} (wf′ c) (wf′ d) w)

∈⊔⁺ˡ : ∀ c d w → w ∈ table c → w ∈ table (c ⊔ᴿ d)
∈⊔⁺ˡ c d w w∈ = subst T (sym (∪-accepts {table c} {table d} (wf′ c) (wf′ d) w)) (from T-∨ (inj₁ w∈))

∈⊔⁺ʳ : ∀ c d w → w ∈ table d → w ∈ table (c ⊔ᴿ d)
∈⊔⁺ʳ c d w w∈ = subst T (sym (∪-accepts {table c} {table d} (wf′ c) (wf′ d) w)) (from T-∨ (inj₂ w∈))

∈⊔⁻ : ∀ c d w → w ∈ table (c ⊔ᴿ d) → w ∈ table c ⊎ w ∈ table d
∈⊔⁻ c d w w∈ = to T-∨ (subst T (∪-accepts {table c} {table d} (wf′ c) (wf′ d) w) w∈)

∈u⁻ : ∀ w → w ∈ table u → w ≡ []
∈u⁻ = ∈⟪⟫⁻ []

∈u⁺ : [] ∈ table u
∈u⁺ = ∈⟪⟫⁺ []

∈tick⁻ : ∀ n w → w ∈ table (of-nat n) → w ≡ replicate n tick
∈tick⁻ n = ∈⟪⟫⁻ (replicate n tick)

∈tick⁺ : ∀ n → replicate n tick ∈ table (of-nat n)
∈tick⁺ n = ∈⟪⟫⁺ (replicate n tick)

∈⊤ : ∀ w → w ∈ table ⊤
∈⊤ = ∈-Σ*

private
  replicate-+ : ∀ {A : Set} m n (x : A) → replicate (m + n) x ≡ replicate m x ++ replicate n x
  replicate-+ zero    n x = refl
  replicate-+ (suc m) n x = cong (x ∷_) (replicate-+ m n x)

------------------------------------------------------------------------
-- The laws
--
-- Proofs go through `subst` along word equations rather than matching
-- on them, so that no table of an operation is ever unfolded.

-- a word of a product is a product of words

∈·-elim : ∀ c d (P : Word → Set) w → w ∈ table (c ·ᴿ d)
        → (∀ x y → x ∈ table c → y ∈ table d → P (x ++ y)) → P w
∈·-elim c d P w w∈ f = go (∈·⁻ c d w w∈)
  where
  go : (∃₂ λ x y → w ≡ x ++ y × x ∈ table c × y ∈ table d) → P w
  go (x , y , eq , x∈ , y∈) = subst P (sym eq) (f x y x∈ y∈)

-- a word of a join is a word of either side

∈⊔-elim : ∀ c d (P : Set) w → w ∈ table (c ⊔ᴿ d)
        → (w ∈ table c → P) → (w ∈ table d → P) → P
∈⊔-elim c d P w w∈ f g = [ f , g ]′ (∈⊔⁻ c d w w∈)

-- two words with product `[]`

∈u-++ˡ : ∀ x y → (x ++ y) ∈ table u → x ≡ []
∈u-++ˡ x y xy∈ = ++-conicalˡ x y (∈u⁻ (x ++ y) xy∈)

∈u-++ʳ : ∀ x y → (x ++ y) ∈ table u → y ≡ []
∈u-++ʳ x y xy∈ = ++-conicalʳ x y (∈u⁻ (x ++ y) xy∈)

·-identityˡ : ∀ c → u ·ᴿ c ≡ c
·-identityˡ c = same-language (u ·ᴿ c) c to′ from′
  where
  to′ : ∀ w → w ∈ table (u ·ᴿ c) → w ∈ table c
  to′ w w∈ = ∈·-elim u c (λ v → v ∈ table c) w w∈ λ x y x∈ y∈ →
    subst (λ v → (v ++ y) ∈ table c) (sym (∈u⁻ x x∈)) y∈

  from′ : ∀ w → w ∈ table c → w ∈ table (u ·ᴿ c)
  from′ w w∈ = subst (λ v → v ∈ table (u ·ᴿ c)) {[] ++ w} {w} refl (∈·⁺ u c [] w ∈u⁺ w∈)

·-identityʳ : ∀ c → c ·ᴿ u ≡ c
·-identityʳ c = same-language (c ·ᴿ u) c to′ from′
  where
  to′ : ∀ w → w ∈ table (c ·ᴿ u) → w ∈ table c
  to′ w w∈ = ∈·-elim c u (λ v → v ∈ table c) w w∈ λ x y x∈ y∈ →
    subst (λ v → v ∈ table c) (sym (trans (cong (x ++_) (∈u⁻ y y∈)) (++-identityʳ x))) x∈

  from′ : ∀ w → w ∈ table c → w ∈ table (c ·ᴿ u)
  from′ w w∈ = subst (λ v → v ∈ table (c ·ᴿ u)) (++-identityʳ w) (∈·⁺ c u w [] w∈ ∈u⁺)

·-assoc : ∀ c d e → (c ·ᴿ d) ·ᴿ e ≡ c ·ᴿ (d ·ᴿ e)
·-assoc c d e = same-language ((c ·ᴿ d) ·ᴿ e) (c ·ᴿ (d ·ᴿ e)) to′ from′
  where
  to′ : ∀ w → w ∈ table ((c ·ᴿ d) ·ᴿ e) → w ∈ table (c ·ᴿ (d ·ᴿ e))
  to′ w w∈ = ∈·-elim (c ·ᴿ d) e (λ v → v ∈ table (c ·ᴿ (d ·ᴿ e))) w w∈ λ xy z xy∈ z∈ →
    ∈·-elim c d (λ v → (v ++ z) ∈ table (c ·ᴿ (d ·ᴿ e))) xy xy∈ λ x y x∈ y∈ →
      subst (λ v → v ∈ table (c ·ᴿ (d ·ᴿ e))) (sym (++-assoc x y z))
            (∈·⁺ c (d ·ᴿ e) x (y ++ z) x∈ (∈·⁺ d e y z y∈ z∈))

  from′ : ∀ w → w ∈ table (c ·ᴿ (d ·ᴿ e)) → w ∈ table ((c ·ᴿ d) ·ᴿ e)
  from′ w w∈ = ∈·-elim c (d ·ᴿ e) (λ v → v ∈ table ((c ·ᴿ d) ·ᴿ e)) w w∈ λ x yz x∈ yz∈ →
    ∈·-elim d e (λ v → (x ++ v) ∈ table ((c ·ᴿ d) ·ᴿ e)) yz yz∈ λ y z y∈ z∈ →
      subst (λ v → v ∈ table ((c ·ᴿ d) ·ᴿ e)) (++-assoc x y z)
            (∈·⁺ (c ·ᴿ d) e (x ++ y) z (∈·⁺ c d x y x∈ y∈) z∈)

≾-refl : ∀ {c} → c ≾ c
≾-refl {c} = ⊆⇒≾ c c λ w w∈ → w∈

≾-trans : ∀ {c d e} → c ≾ d → d ≾ e → c ≾ e
≾-trans {c} {d} {e} p q = ⊆⇒≾ c e λ w w∈ → ≾⇒⊆ d e q w (≾⇒⊆ c d p w w∈)

≾-antisym : ∀ {c d} → c ≾ d → d ≾ c → c ≡ d
≾-antisym {c} {d} p q = same-language c d (≾⇒⊆ c d p) (≾⇒⊆ d c q)

≾-⊤ : ∀ c → c ≾ ⊤
≾-⊤ c = ⊆⇒≾ c ⊤ λ w _ → ∈⊤ w

⊔-ubˡ : ∀ c d → c ≾ c ⊔ᴿ d
⊔-ubˡ c d = ⊆⇒≾ c (c ⊔ᴿ d) (∈⊔⁺ˡ c d)

⊔-ubʳ : ∀ c d → d ≾ c ⊔ᴿ d
⊔-ubʳ c d = ⊆⇒≾ d (c ⊔ᴿ d) (∈⊔⁺ʳ c d)

⊔-lub : ∀ {c d e} → c ≾ e → d ≾ e → c ⊔ᴿ d ≾ e
⊔-lub {c} {d} {e} p q = ⊆⇒≾ (c ⊔ᴿ d) e λ w w∈ →
  ∈⊔-elim c d (w ∈ table e) w w∈ (≾⇒⊆ c e p w) (≾⇒⊆ d e q w)

·-monoˡ-≾ : ∀ {c d d′} → d ≾ d′ → d ·ᴿ c ≾ d′ ·ᴿ c
·-monoˡ-≾ {c} {d} {d′} p = ⊆⇒≾ (d ·ᴿ c) (d′ ·ᴿ c) λ w w∈ →
  ∈·-elim d c (λ v → v ∈ table (d′ ·ᴿ c)) w w∈ λ x y x∈ y∈ →
    ∈·⁺ d′ c x y (≾⇒⊆ d d′ p x x∈) y∈

·-monoʳ-≾ : ∀ {c d d′} → d ≾ d′ → c ·ᴿ d ≾ c ·ᴿ d′
·-monoʳ-≾ {c} {d} {d′} p = ⊆⇒≾ (c ·ᴿ d) (c ·ᴿ d′) λ w w∈ →
  ∈·-elim c d (λ v → v ∈ table (c ·ᴿ d′)) w w∈ λ x y x∈ y∈ →
    ∈·⁺ c d′ x y x∈ (≾⇒⊆ d d′ p y y∈)

·-distribˡ-⊔-≾ : ∀ c d e → c ·ᴿ (d ⊔ᴿ e) ≾ (c ·ᴿ d) ⊔ᴿ (c ·ᴿ e)
·-distribˡ-⊔-≾ c d e = ⊆⇒≾ (c ·ᴿ (d ⊔ᴿ e)) ((c ·ᴿ d) ⊔ᴿ (c ·ᴿ e)) λ w w∈ →
  ∈·-elim c (d ⊔ᴿ e) (λ v → v ∈ table ((c ·ᴿ d) ⊔ᴿ (c ·ᴿ e))) w w∈ λ x y x∈ y∈ →
    ∈⊔-elim d e ((x ++ y) ∈ table ((c ·ᴿ d) ⊔ᴿ (c ·ᴿ e))) y y∈
      (λ y∈d → ∈⊔⁺ˡ (c ·ᴿ d) (c ·ᴿ e) (x ++ y) (∈·⁺ c d x y x∈ y∈d))
      (λ y∈e → ∈⊔⁺ʳ (c ·ᴿ d) (c ·ᴿ e) (x ++ y) (∈·⁺ c e x y x∈ y∈e))

·-distribʳ-⊔-≾ : ∀ c d e → (d ⊔ᴿ e) ·ᴿ c ≾ (d ·ᴿ c) ⊔ᴿ (e ·ᴿ c)
·-distribʳ-⊔-≾ c d e = ⊆⇒≾ ((d ⊔ᴿ e) ·ᴿ c) ((d ·ᴿ c) ⊔ᴿ (e ·ᴿ c)) λ w w∈ →
  ∈·-elim (d ⊔ᴿ e) c (λ v → v ∈ table ((d ·ᴿ c) ⊔ᴿ (e ·ᴿ c))) w w∈ λ x y x∈ y∈ →
    ∈⊔-elim d e ((x ++ y) ∈ table ((d ·ᴿ c) ⊔ᴿ (e ·ᴿ c))) x x∈
      (λ x∈d → ∈⊔⁺ˡ (d ·ᴿ c) (e ·ᴿ c) (x ++ y) (∈·⁺ d c x y x∈d y∈))
      (λ x∈e → ∈⊔⁺ʳ (d ·ᴿ c) (e ·ᴿ c) (x ++ y) (∈·⁺ e c x y x∈e y∈))

≾-zero-productˡ : ∀ {c d} → c ·ᴿ d ≾ u → c ≾ u
≾-zero-productˡ {c} {d} p = ⊆⇒≾ c u λ x x∈ → go x x∈ (inhabited′ d)
  where
  go : ∀ x → x ∈ table c → (∃ λ y → y ∈ table d) → x ∈ table u
  go x x∈ (y , y∈) =
    subst (λ v → v ∈ table u) (sym (∈u-++ˡ x y (≾⇒⊆ (c ·ᴿ d) u p (x ++ y) (∈·⁺ c d x y x∈ y∈)))) ∈u⁺

≾-zero-productʳ : ∀ {c d} → c ·ᴿ d ≾ u → d ≾ u
≾-zero-productʳ {c} {d} p = ⊆⇒≾ d u λ y y∈ → go y y∈ (inhabited′ c)
  where
  go : ∀ y → y ∈ table d → (∃ λ x → x ∈ table c) → y ∈ table u
  go y y∈ (x , x∈) =
    subst (λ v → v ∈ table u) (sym (∈u-++ʳ x y (≾⇒⊆ (c ·ᴿ d) u p (x ++ y) (∈·⁺ c d x y x∈ y∈)))) ∈u⁺

of-nat-zero : of-nat 0 ≡ u
of-nat-zero = same-language (of-nat 0) u
  (λ w w∈ → subst (λ v → v ∈ table u) {[]} {w} (sym (∈tick⁻ 0 w w∈)) ∈u⁺)
  (λ w w∈ → subst (λ v → v ∈ table (of-nat 0)) {replicate 0 tick} {w} (sym (∈u⁻ w w∈)) (∈tick⁺ 0))

of-nat-plus : ∀ {m n} → of-nat (m + n) ≡ of-nat m ·ᴿ of-nat n
of-nat-plus {m} {n} = same-language (of-nat (m + n)) (of-nat m ·ᴿ of-nat n) to′ from′
  where
  to′ : ∀ w → w ∈ table (of-nat (m + n)) → w ∈ table (of-nat m ·ᴿ of-nat n)
  to′ w w∈ =
    subst (λ v → v ∈ table (of-nat m ·ᴿ of-nat n))
          (sym (trans (∈tick⁻ (m + n) w w∈) (replicate-+ m n tick)))
          (∈·⁺ (of-nat m) (of-nat n) (replicate m tick) (replicate n tick) (∈tick⁺ m) (∈tick⁺ n))

  from′ : ∀ w → w ∈ table (of-nat m ·ᴿ of-nat n) → w ∈ table (of-nat (m + n))
  from′ w w∈ = ∈·-elim (of-nat m) (of-nat n) (λ v → v ∈ table (of-nat (m + n))) w w∈ λ x y x∈ y∈ →
    subst (λ v → v ∈ table (of-nat (m + n)))
          (sym (trans (cong₂ _++_ (∈tick⁻ m x x∈) (∈tick⁻ n y y∈)) (sym (replicate-+ m n tick))))
          (∈tick⁺ (m + n))

------------------------------------------------------------------------
-- The grade

regular-grade : Grade
regular-grade = record
  { Carrier         = Regular
  ; _·_             = _·ᴿ_
  ; u               = u
  ; _≾_             = _≾_
  ; ⊤               = ⊤
  ; _⊔_             = _⊔ᴿ_
  ; of-nat          = of-nat
  ; ·-identityˡ     = ·-identityˡ
  ; ·-identityʳ     = ·-identityʳ
  ; ·-assoc         = ·-assoc
  ; ≾-refl          = λ {c} → ≾-refl {c}
  ; ≾-trans         = λ {c} {d} {e} → ≾-trans {c} {d} {e}
  ; ≾-antisym       = λ {c} {d} → ≾-antisym {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → T-irrelevant
  ; _≾?_            = λ c d → T? (table c ⊆ᵇ table d)
  ; ≾-⊤             = ≾-⊤
  ; ⊔-ubˡ           = ⊔-ubˡ
  ; ⊔-ubʳ           = ⊔-ubʳ
  ; ⊔-lub           = λ {c} {d} {e} → ⊔-lub {c} {d} {e}
  ; ·-monoˡ-≾       = λ {c} {d} {d′} → ·-monoˡ-≾ {c} {d} {d′}
  ; ·-monoʳ-≾       = λ {c} {d} {d′} → ·-monoʳ-≾ {c} {d} {d′}
  ; ·-distribˡ-⊔-≾  = ·-distribˡ-⊔-≾
  ; ·-distribʳ-⊔-≾  = ·-distribʳ-⊔-≾
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  ; u-least?        = nothing
  ; ·-comm?         = nothing
  }
