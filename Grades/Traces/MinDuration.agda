--------------------------------------------------------------------------
-- Best-case durations: the least duration of a set of timed traces     --
--                                                                      --
-- `minSetDuration` measures a set by its shortest trace, the time      --
-- taken when the computation realises its fastest run, as              --
-- `setDuration` of `MaxDuration.agda` measures it by its longest. The  --
-- per-trace `duration` is that of `Durations.agda`.                    --
--------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻;
         ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊓_; _≤_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-antisym; +-mono-≤;
         m⊓n≤m; m⊓n≤n; ⊓-glb; ⊓-sel)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ)

module Grades.Traces.MinDuration
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_) where

open import Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Grades.Traces.Durations ℕᵀ Op

open WithDecEq _≟ₒ_

------------------------------------------------------------------------
-- The minimum of a seed and a list of naturals
--
-- `min` has no identity in `ℕ`, so the first element of a non-empty
-- list is threaded through as a seed.

minWith : ℕ → List ℕ → ℕ
minWith a []       = a
minWith a (x ∷ xs) = x ⊓ minWith a xs

-- the result is below the seed and below every list element

minWith-≤seed : (a : ℕ) (xs : List ℕ) → minWith a xs ≤ a
minWith-≤seed a []       = ≤-refl
minWith-≤seed a (x ∷ xs) = ≤-trans (m⊓n≤n x (minWith a xs)) (minWith-≤seed a xs)

minWith-≤mem : (a v : ℕ) (xs : List ℕ) → v ∈ xs → minWith a xs ≤ v
minWith-≤mem a v (x ∷ xs) (here refl) = m⊓n≤m x (minWith a xs)
minWith-≤mem a v (x ∷ xs) (there mem) =
  ≤-trans (m⊓n≤n x (minWith a xs)) (minWith-≤mem a v xs mem)

-- it is the greatest such lower bound

minWith-glb : (a b : ℕ) (xs : List ℕ)
            → b ≤ a → (∀ v → v ∈ xs → b ≤ v) → b ≤ minWith a xs
minWith-glb a b []       b≤a h = b≤a
minWith-glb a b (x ∷ xs) b≤a h =
  ⊓-glb (h x (here refl)) (minWith-glb a b xs b≤a (λ v mem → h v (there mem)))

-- the minimum is attained, either at the seed or at a list element

minWith-attained : (a : ℕ) (xs : List ℕ)
                 → (minWith a xs ≡ a) ⊎ Σ ℕ (λ v → (v ∈ xs) × (minWith a xs ≡ v))
minWith-attained a []       = inj₁ refl
minWith-attained a (x ∷ xs) with ⊓-sel x (minWith a xs)
... | inj₁ eq = inj₂ (x , here refl , eq)
... | inj₂ eq with minWith-attained a xs
...   | inj₁ eqa            = inj₁ (trans eq eqa)
...   | inj₂ (v , mem , eqv) = inj₂ (v , there mem , trans eq eqv)

------------------------------------------------------------------------
-- The least duration of a non-empty list of traces

bigMin : List ℕ → ℕ
bigMin []       = zero
bigMin (x ∷ xs) = minWith x xs

-- every member's value is above the minimum

bigMin-mem : (f : Trace → ℕ) (t : Trace) (xs : List Trace)
           → t ∈ xs → bigMin (map f xs) ≤ f t
bigMin-mem f t (x ∷ xs) (here refl) = minWith-≤seed (f x) (map f xs)
bigMin-mem f t (x ∷ xs) (there mem) =
  minWith-≤mem (f x) (f t) (map f xs) (∈-map⁺ f mem)

-- the minimum is the greatest lower bound

bigMin-bound : (f : Trace → ℕ) (xs : List Trace) (b : ℕ)
             → NonEmpty xs → (∀ t → t ∈ xs → b ≤ f t) → b ≤ bigMin (map f xs)
bigMin-bound f []       b () _
bigMin-bound f (x ∷ xs) b _  h =
  minWith-glb (f x) b (map f xs) (h x (here refl)) bound-tail
  where
    bound-tail : (v : ℕ) → v ∈ map f xs → b ≤ v
    bound-tail v v∈ with ∈-map⁻ f v∈
    ... | t , t∈xs , refl = h t (there t∈xs)

-- the minimum is attained at some member

bigMin-attained : (f : Trace → ℕ) (x : Trace) (xs : List Trace)
                → Σ Trace (λ t → (t ∈ (x ∷ xs)) × (bigMin (map f (x ∷ xs)) ≡ f t))
bigMin-attained f x xs with minWith-attained (f x) (map f xs)
... | inj₁ eq            = x , here refl , eq
... | inj₂ (v , v∈ , eq) with ∈-map⁻ f v∈
...   | t , t∈xs , refl  = t , there t∈xs , eq

-- the minimum is monotone in the measured function

bigMin-mono : (f g : Trace → ℕ) (xs : List Trace)
            → NonEmpty xs → (∀ t → f t ≤ g t)
            → bigMin (map f xs) ≤ bigMin (map g xs)
bigMin-mono f g xs ne h =
  bigMin-bound g xs (bigMin (map f xs)) ne
    (λ t t∈xs → ≤-trans (bigMin-mem f t xs t∈xs) (h t))

-- `bigMin` is a semigroup homomorphism from non-empty lists under `++` to
-- `(ℕ, ⊓)`, both arguments taken in cons form as `NonEmpty` is defined on
-- `List Trace` only

bigMin-++ : (a : ℕ) (as : List ℕ) (b : ℕ) (bs : List ℕ)
          → bigMin ((a ∷ as) ++ (b ∷ bs)) ≡ bigMin (a ∷ as) ⊓ bigMin (b ∷ bs)
bigMin-++ a as b bs = ≤-antisym le ge
  where
    xs++ys : List ℕ
    xs++ys = as ++ (b ∷ bs)

    -- the minimum of the concatenation is below the minimum of each half,
    -- via the value at which that half's minimum is attained
    le : bigMin ((a ∷ as) ++ (b ∷ bs)) ≤ bigMin (a ∷ as) ⊓ bigMin (b ∷ bs)
    le = ⊓-glb le-l le-r
      where
        le-l : minWith a xs++ys ≤ minWith a as
        le-l with minWith-attained a as
        ... | inj₁ eq            = ≤-trans (minWith-≤seed a xs++ys) (≤-reflexive (sym eq))
        ... | inj₂ (v , mem , eq) =
          ≤-trans (minWith-≤mem a v xs++ys (∈-++⁺ˡ mem)) (≤-reflexive (sym eq))

        le-r : minWith a xs++ys ≤ minWith b bs
        le-r with minWith-attained b bs
        ... | inj₁ eq =
          ≤-trans (minWith-≤mem a b xs++ys (∈-++⁺ʳ as (here refl))) (≤-reflexive (sym eq))
        ... | inj₂ (v , mem , eq) =
          ≤-trans (minWith-≤mem a v xs++ys (∈-++⁺ʳ as (there mem))) (≤-reflexive (sym eq))

    -- conversely the meet of the two halves' minima lower-bounds every
    -- element of the concatenation, hence lower-bounds its minimum
    ge : bigMin (a ∷ as) ⊓ bigMin (b ∷ bs) ≤ bigMin ((a ∷ as) ++ (b ∷ bs))
    ge = minWith-glb a (minWith a as ⊓ minWith b bs) xs++ys
           (≤-trans (m⊓n≤m (minWith a as) (minWith b bs)) (minWith-≤seed a as))
           bound
      where
        bound : (v : ℕ) → v ∈ xs++ys → minWith a as ⊓ minWith b bs ≤ v
        bound v v∈ with ∈-++⁻ as v∈
        ... | inj₁ v∈as = ≤-trans (m⊓n≤m (minWith a as) (minWith b bs)) (minWith-≤mem a v as v∈as)
        ... | inj₂ (here refl) =
          ≤-trans (m⊓n≤n (minWith a as) (minWith b bs)) (minWith-≤seed b bs)
        ... | inj₂ (there v∈bs) =
          ≤-trans (m⊓n≤n (minWith a as) (minWith b bs)) (minWith-≤mem b v bs v∈bs)

------------------------------------------------------------------------
-- Best-case durations relative to a fixed cost on operation symbols
--
-- A set of traces is measured by its least member, at the per-trace
-- `duration` of `Durations.agda`.

module MinDurations (c : Op → ℕ) where

  open Durations c public

  -- the best-case duration of a set of traces is the least duration of
  -- a member

  minSetDuration : List Trace → ℕ
  minSetDuration xs = bigMin (map duration xs)

  -- `minSetDuration` is antitone for the subset order: enlarging a set
  -- can only lower its minimum

  minSetDuration-⊒ : (xs ys : List Trace)
                   → NonEmpty xs → xs ⊑ ys → minSetDuration ys ≤ minSetDuration xs
  minSetDuration-⊒ xs ys ne sub =
    bigMin-bound duration xs (minSetDuration ys) ne
      (λ t t∈xs → bigMin-mem duration t ys (toWitness (sub t (fromWitness t∈xs))))

  -- `minSetDuration` is a semigroup homomorphism from concatenation of
  -- non-empty sets of traces to `(ℕ, ⊓)`

  minSetDuration-++ : (xs ys : List Trace) → NonEmpty xs → NonEmpty ys
                    → minSetDuration (xs ++ ys) ≡ minSetDuration xs ⊓ minSetDuration ys
  minSetDuration-++ []       ys       () _
  minSetDuration-++ (x ∷ xs) []       _  ()
  minSetDuration-++ (x ∷ xs) (y ∷ ys) _  _ =
    trans (cong bigMin (map-++ duration (x ∷ xs) (y ∷ ys)))
          (bigMin-++ (duration x) (map duration xs) (duration y) (map duration ys))

  -- `minSetDuration` is a monoid homomorphism for the language product
  -- of (non-empty) sets of traces

  minSetDuration-·ˢ : (xs ys : List Trace)
                    → NonEmpty xs → NonEmpty ys
                    → minSetDuration (xs ·ˢ ys) ≡ minSetDuration xs + minSetDuration ys
  minSetDuration-·ˢ []       ys       () _
  minSetDuration-·ˢ (x ∷ xs) []       _  ()
  minSetDuration-·ˢ (x ∷ xs) (y ∷ ys) _  _ = ≤-antisym le ge
    where
      -- the minimum of the product is attained by the fastest member of
      -- each factor sequenced together
      le : minSetDuration ((x ∷ xs) ·ˢ (y ∷ ys))
         ≤ minSetDuration (x ∷ xs) + minSetDuration (y ∷ ys)
      le with bigMin-attained duration x xs | bigMin-attained duration y ys
      ... | p , p∈ , peq | q , q∈ , qeq =
        ≤-trans (bigMin-mem duration (p ∙ q) ((x ∷ xs) ·ˢ (y ∷ ys))
                   (∈-cartesianProductWith⁺ _∙_ p∈ q∈))
                (≤-reflexive (trans (duration-∙ p q)
                                    (cong₂ _+_ (sym peq) (sym qeq))))

      -- conversely every product member is at least the sum of the minima
      ge : minSetDuration (x ∷ xs) + minSetDuration (y ∷ ys)
         ≤ minSetDuration ((x ∷ xs) ·ˢ (y ∷ ys))
      ge = bigMin-bound duration ((x ∷ xs) ·ˢ (y ∷ ys))
             (minSetDuration (x ∷ xs) + minSetDuration (y ∷ ys))
             (·ˢ-ne {x ∷ xs} {y ∷ ys} _ _) bound
        where
          bound : (r : Trace) → r ∈ ((x ∷ xs) ·ˢ (y ∷ ys))
                → minSetDuration (x ∷ xs) + minSetDuration (y ∷ ys) ≤ duration r
          bound r r∈ with ∈-cartesianProductWith⁻ _∙_ (x ∷ xs) (y ∷ ys) r∈
          ... | a , b , a∈ , b∈ , refl =
            ≤-trans (+-mono-≤ (bigMin-mem duration a (x ∷ xs) a∈)
                              (bigMin-mem duration b (y ∷ ys) b∈))
                    (≤-reflexive (sym (duration-∙ a b)))

  -- normalising a list leaves its duration alone, the members being the
  -- same, so the duration of a union is the better of the two, and that
  -- of a language product the sum

  minSetDuration-nf : (xs : List Trace) → NonEmpty xs
                    → minSetDuration (nf xs) ≡ minSetDuration xs
  minSetDuration-nf xs ne =
    ≤-antisym
      (bigMin-bound duration xs (minSetDuration (nf xs)) ne
        (λ t t∈ → bigMin-mem duration t (nf xs) (nf-∈⁺ t∈)))
      (bigMin-bound duration (nf xs) (minSetDuration xs) (nf-ne xs ne)
        (λ t t∈ → bigMin-mem duration t xs (nf-∈⁻ t∈)))

  minSetDuration-∪ˢ : (xs ys : List Trace) → NonEmpty xs → NonEmpty ys
                    → minSetDuration (xs ∪ˢ ys)
                    ≡ minSetDuration xs ⊓ minSetDuration ys
  minSetDuration-∪ˢ xs ys nx ny =
    trans (minSetDuration-nf (xs ++ ys) (++-ne nx ny))
          (minSetDuration-++ xs ys nx ny)

  minSetDuration-nf-·ˢ : (xs ys : List Trace) → NonEmpty xs → NonEmpty ys
                       → minSetDuration (nf (xs ·ˢ ys))
                       ≡ minSetDuration xs + minSetDuration ys
  minSetDuration-nf-·ˢ xs ys nx ny =
    trans (minSetDuration-nf (xs ·ˢ ys) (·ˢ-ne nx ny))
          (minSetDuration-·ˢ xs ys nx ny)

------------------------------------------------------------------------
-- Comparing best-case durations across two different costs
--
-- `minSetDuration` is monotone in the cost: a pointwise larger cost can
-- only raise the best-case duration.

minSetDuration-cost : (c c' : Op → ℕ) (xs : List Trace)
                    → NonEmpty xs → (∀ o → c o ≤ c' o)
                    → MinDurations.minSetDuration c xs ≤ MinDurations.minSetDuration c' xs
minSetDuration-cost c c' xs ne h =
  bigMin-mono (Durations.duration c) (Durations.duration c') xs ne (duration-mono c c' h)
