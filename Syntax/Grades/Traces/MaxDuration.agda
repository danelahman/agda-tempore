------------------------------------------------------------------------
-- Worst-case durations: the *greatest* duration of a set of timed    --
-- traces, relative to a cost on operation symbols.                    --
--                                                                     --
-- The per-trace `duration` is shared with `MinDuration.agda` and      --
-- lives in `Durations.agda`; only the set-level aggregation -- here   --
-- the `⊔`-based worst case -- is specific to this module.             --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Data.List.Base
  using (List; []; _∷_; [_]; _++_; map; foldr)
open import Data.List.Properties using (map-++; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; _+_; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; +-distribˡ-⊔; +-distribʳ-⊔; ⊔-assoc;
         ⊔-identityʳ; ⊔-lub; ⊔-mono-≤; m≤m⊔n; m≤n⊔m)

open import Util.Equality

module Syntax.Grades.Traces.MaxDuration (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open WithDecEq _≟ₒ_

------------------------------------------------------------------------
-- The (greatest) of a list of durations

bigMax : List ℕ → ℕ
bigMax = foldr _⊔_ zero

-- `bigMax` is a monoid homomorphism `(List ℕ, ++) → (ℕ, ⊔)`

bigMax-++ : (as bs : List ℕ) → bigMax (as ++ bs) ≡ bigMax as ⊔ bigMax bs
bigMax-++ []       bs = refl
bigMax-++ (a ∷ as) bs =
  trans (cong (a ⊔_) (bigMax-++ as bs))
        (sym (⊔-assoc a (bigMax as) (bigMax bs)))

-- on a non-empty list, adding a constant to every element shifts the
-- maximum by that constant

bigMax-+ : (a z : ℕ) (zs : List ℕ)
         → bigMax (map (a +_) (z ∷ zs)) ≡ a + bigMax (z ∷ zs)
bigMax-+ a z [] =
  trans (⊔-identityʳ (a + z)) (cong (a +_) (sym (⊔-identityʳ z)))
bigMax-+ a z (w ∷ zs) =
  trans (cong ((a + z) ⊔_) (bigMax-+ a w zs))
        (sym (+-distribˡ-⊔ a z (bigMax (w ∷ zs))))

-- every member's value is below the maximum

bigMax-mem : (f : Trace → ℕ) (t : Trace) (xs : List Trace)
           → t ∈ xs → f t ≤ bigMax (map f xs)
bigMax-mem f t (x ∷ xs) (here eq) =
  ≤-trans (≤-reflexive (cong f eq)) (m≤m⊔n (f x) (bigMax (map f xs)))
bigMax-mem f t (x ∷ xs) (there mem) =
  ≤-trans (bigMax-mem f t xs mem) (m≤n⊔m (f x) (bigMax (map f xs)))

-- the maximum is the least upper bound

bigMax-bound : (f : Trace → ℕ) (xs : List Trace) (b : ℕ)
             → (∀ t → t ∈ xs → f t ≤ b) → bigMax (map f xs) ≤ b
bigMax-bound f []       b h = z≤n
bigMax-bound f (x ∷ xs) b h =
  ⊔-lub (h x (here refl)) (bigMax-bound f xs b (λ t mem → h t (there mem)))

-- the maximum is monotone in the measured function

bigMax-mono : (f g : Trace → ℕ) (xs : List Trace)
            → (∀ t → f t ≤ g t) → bigMax (map f xs) ≤ bigMax (map g xs)
bigMax-mono f g []       h = z≤n
bigMax-mono f g (x ∷ xs) h = ⊔-mono-≤ (h x) (bigMax-mono f g xs h)

------------------------------------------------------------------------
-- Worst-case durations relative to a fixed cost on operation symbols
--
-- We reuse the per-trace `duration` of `Durations.agda` and aggregate
-- a set of traces by its greatest (worst-case) member.

module MaxDurations (c : Op → ℕ) where

  open Durations c public

  --------------------------------------------------------------------
  -- The duration of a set of traces is the greatest duration of a member

  setDuration : List Trace → ℕ
  setDuration xs = bigMax (map duration xs)

  -- `setDuration` is additive over list concatenation (as a `⊔`-monoid map)

  setDuration-++ : (as bs : List Trace)
                 → setDuration (as ++ bs) ≡ setDuration as ⊔ setDuration bs
  setDuration-++ as bs =
    trans (cong bigMax (map-++ duration as bs))
          (bigMax-++ (map duration as) (map duration bs))

  -- measuring after sequencing with a fixed `x` adds `duration x`

  map-duration-∙ : (x : Trace) (ys : List Trace)
                 → map duration (map (x ∙_) ys) ≡ map ((duration x) +_) (map duration ys)
  map-duration-∙ x []       = refl
  map-duration-∙ x (y ∷ ys) = cong₂ _∷_ (duration-∙ x y) (map-duration-∙ x ys)

  setDuration-map-∙ : (x y : Trace) (ys : List Trace)
                    → setDuration (map (x ∙_) (y ∷ ys)) ≡ duration x + setDuration (y ∷ ys)
  setDuration-map-∙ x y ys =
    trans (cong bigMax (map-duration-∙ x (y ∷ ys)))
          (bigMax-+ (duration x) (duration y) (map duration ys))

  -- `setDuration` is a monoid homomorphism for the language product of
  -- non-empty sets of traces

  setDuration-·ˢ : (xs ys : List Trace)
                 → NonEmpty xs → NonEmpty ys
                 → setDuration (xs ·ˢ ys) ≡ setDuration xs + setDuration ys
  setDuration-·ˢ []            ys       ()  _
  setDuration-·ˢ (x ∷ xs)      []       _   ()
  setDuration-·ˢ (x ∷ [])      (y ∷ ys) _   _ =
    trans (cong setDuration (++-identityʳ (map (x ∙_) (y ∷ ys))))
          (trans (setDuration-map-∙ x y ys)
                 (cong (_+ setDuration (y ∷ ys)) (sym (⊔-identityʳ (duration x)))))
  setDuration-·ˢ (x ∷ x' ∷ xs) (y ∷ ys) _   _ =
    trans (setDuration-++ (map (x ∙_) (y ∷ ys)) ((x' ∷ xs) ·ˢ (y ∷ ys)))
          (trans (cong₂ _⊔_ (setDuration-map-∙ x y ys)
                            (setDuration-·ˢ (x' ∷ xs) (y ∷ ys) _ _))
                 (sym (+-distribʳ-⊔ (setDuration (y ∷ ys))
                                    (duration x) (setDuration (x' ∷ xs)))))

  -- `setDuration` is monotone for the subset order on sets of traces

  setDuration-⊑ : (xs ys : List Trace)
                → xs ⊑ ys → setDuration xs ≤ setDuration ys
  setDuration-⊑ xs ys sub =
    bigMax-bound duration xs (setDuration ys)
      (λ t t∈xs → bigMax-mem duration t ys (toWitness (sub t (fromWitness t∈xs))))

------------------------------------------------------------------------
-- Comparing worst-case durations across two different costs

open MaxDurations

-- `setDuration` is monotone in the cost

setDuration-cost : (c c' : Op → ℕ) (xs : List Trace)
                 → (∀ o → c o ≤ c' o) → setDuration c xs ≤ setDuration c' xs
setDuration-cost c c' xs h = bigMax-mono (duration c) (duration c') xs (duration-mono c c' h)
