------------------------------------------------------------------------
-- Counts and time: no count grade projects onto time, and a cost     --
-- model preserves all but the join when time is paired with the      --
-- counts.                                                            --
--                                                                    --
-- In a count grade, `n` time steps are the unit for every `n`, so    --
-- `ι 1` and `ι 0` coincide; a time grade distinguishes               --
-- them, so no morphism from counts to time preserves `ι`.            --
--                                                                    --
-- A cost model `ks` weighs the counters, and `weigh ks` sums the     --
-- weighted counts in `G`, the bound of each counter taken `k` times. --
-- With time paired alongside, as `counts ×ᵍ time` with               --
--                                                                    --
--   (c , t)  ↦  t · weigh ks c                                       --
--                                                                    --
-- the unit, the product, monotonicity, the inclusion of ℕ and the    --
-- greatest grade are preserved (the last where the top of `G` is     --
-- absorbing or is the unit). The join is not: the join of counts is  --
-- pointwise and may combine the worst case of one counter in one run --
-- with that of another counter in a different run, whose weighted    --
-- sum exceeds the weights of both runs. `weigh` is lax: the join of  --
-- the images lies below the image of the join.                       --
------------------------------------------------------------------------

open import Grades.Durations using (Duration)
open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base

module Grades.Examples.System.Counts.Time where

open import Algebra.Definitions using (Commutative)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Util.Equality

import Grades.Examples.Counts.Power as Power

------------------------------------------------------------------------
-- No projection onto a grade that counts time

module _ (G H : Grade ℕᴰ) where

  open Power G using (power)
  open Grade H using () renaming (_≃_ to _≃H_)

  no-projection : ∀ {n} → ¬ (Grade.ι H 1 ≃H Grade.ι H 0)
                → ¬ (power n →ᵍ H)
  no-projection ne F = ne (≃-trans (≃-sym (map-ι {1})) (map-ι {0}))
    where open _→ᵍ_ F
          open Grade H using (≃-trans; ≃-sym)

-- at the two time grades the counts are built from

open import Grades.Examples.Time.UpperBound
  using (upper-bound)
open import Grades.Examples.Time.LowerBound
  using (lower-bound)
open import Grades.Examples.Counts.AtMost using (at-most-counts)
open import Grades.Examples.Counts.AtLeast using (at-least-counts)

no-at-most-counts→upper-bounds :
  ∀ {n} → ¬ (at-most-counts n →ᵍ upper-bound)
no-at-most-counts→upper-bounds =
  no-projection upper-bound upper-bound
    λ e → toWitnessFalse
            {a? = Grade._≾?_ upper-bound
                    (Grade.ι upper-bound 1) (Grade.ι upper-bound 0)}
            _ (proj₁ e)

no-at-least-counts→lower-bounds :
  ∀ {n} → ¬ (at-least-counts n →ᵍ lower-bound)
no-at-least-counts→lower-bounds =
  no-projection lower-bound lower-bound
    λ e → toWitnessFalse
            {a? = Grade._≾?_ lower-bound
                    (Grade.ι lower-bound 0) (Grade.ι lower-bound 1)}
            _ (proj₂ e)

------------------------------------------------------------------------
-- Weighted sums, in a commutative grade

module Weigh {D : Duration} (G : Grade D) (comm : Commutative (Grade._≃_ G) (Grade._·_ G)) where

  open Grade G renaming (Carrier to C)
  open Power G using (_·ᵛ_; _⊔ᵛ_; 𝟏ᵛ; ⊤ᵛ; _≾ᵛ_; ⊔ᵛ-ubˡ; ⊔ᵛ-ubʳ)

  -- `k` copies of a grade in sequence

  times : ℕ → C → C
  times zero    a = 𝟏
  times (suc k) a = a · times k a

  -- the middle-four interchange

  interchange : (a b c d : C) → (a · b) · (c · d) ≃ (a · c) · (b · d)
  interchange a b c d =
    ≃-trans (·-assoc a b (c · d))
    (≃-trans (·-cong ≃-refl (≃-sym (·-assoc b c d)))
    (≃-trans (·-cong ≃-refl (·-cong (comm b c) ≃-refl))
    (≃-trans (·-cong ≃-refl (·-assoc c b d))
             (≃-sym (·-assoc a c (b · d))))))

  times-𝟏 : (k : ℕ) → times k 𝟏 ≃ 𝟏
  times-𝟏 zero    = ≃-refl
  times-𝟏 (suc k) = ≃-trans (·-identityˡ (times k 𝟏)) (times-𝟏 k)

  times-· : (k : ℕ) (a b : C) → times k (a · b) ≃ times k a · times k b
  times-· zero    a b = ≃-sym (·-identityˡ 𝟏)
  times-· (suc k) a b =
    ≃-trans (·-cong ≃-refl (times-· k a b))
            (interchange a b (times k a) (times k b))

  times-mono : (k : ℕ) {a b : C} → a ≾ b → times k a ≾ times k b
  times-mono zero    p = ≾-refl
  times-mono (suc k) p = ≾-trans (·-monoˡ-≾ p) (·-monoʳ-≾ (times-mono k p))

  -- the weighted sum of a vector of counts

  weigh : ∀ {n} → Vec ℕ n → Vec C n → C
  weigh []       []       = 𝟏
  weigh (k ∷ ks) (a ∷ as) = times k a · weigh ks as

  weigh-𝟏 : ∀ {n} (ks : Vec ℕ n) → weigh ks 𝟏ᵛ ≃ 𝟏
  weigh-𝟏 []       = ≃-refl
  weigh-𝟏 (k ∷ ks) = ≃-trans (·-cong (times-𝟏 k) (weigh-𝟏 ks)) (·-identityˡ 𝟏)

  weigh-· : ∀ {n} (ks : Vec ℕ n) (c d : Vec C n)
          → weigh ks (c ·ᵛ d) ≃ weigh ks c · weigh ks d
  weigh-· []       []       []       = ≃-sym (·-identityˡ 𝟏)
  weigh-· (k ∷ ks) (a ∷ as) (b ∷ bs) =
    ≃-trans (·-cong (times-· k a b) (weigh-· ks as bs))
            (interchange (times k a) (times k b) (weigh ks as) (weigh ks bs))

  weigh-mono : ∀ {n} (ks : Vec ℕ n) {c d : Vec C n} → c ≾ᵛ d → weigh ks c ≾ weigh ks d
  weigh-mono []       {[]}    {[]}    _       = ≾-refl
  weigh-mono (k ∷ ks) {_ ∷ _} {_ ∷ _} (p , ps) =
    ≾-trans (·-monoˡ-≾ (times-mono k p)) (·-monoʳ-≾ (weigh-mono ks ps))

  -- the join is preserved laxly: the join of the images lies below the
  -- image of the join

  weigh-⊔-lax : ∀ {n} (ks : Vec ℕ n) (c d : Vec C n)
              → weigh ks c ⊔ weigh ks d ≾ weigh ks (c ⊔ᵛ d)
  weigh-⊔-lax ks c d =
    ⊔-lub (weigh-mono ks (⊔ᵛ-ubˡ c d)) (weigh-mono ks (⊔ᵛ-ubʳ c d))

  --------------------------------------------------------------------
  -- Paired with time: `(c , t) ↦ t · weigh ks c`

  paired : ∀ {n} → Vec ℕ n → Vec C n → C → C
  paired ks c t = t · weigh ks c

  paired-𝟏 : ∀ {n} (ks : Vec ℕ n) → paired ks 𝟏ᵛ 𝟏 ≃ 𝟏
  paired-𝟏 ks = ≃-trans (·-cong ≃-refl (weigh-𝟏 ks)) (·-identityˡ 𝟏)

  paired-ι : ∀ {n} (ks : Vec ℕ n) (τ : Duration.Carrier D)
                → paired ks 𝟏ᵛ (ι τ) ≃ ι τ
  paired-ι ks τ = ≃-trans (·-cong ≃-refl (weigh-𝟏 ks)) (·-identityʳ (ι τ))

  paired-· : ∀ {n} (ks : Vec ℕ n) (c d : Vec C n) (s t : C)
           → paired ks (c ·ᵛ d) (s · t) ≃ paired ks c s · paired ks d t
  paired-· ks c d s t =
    ≃-trans (·-cong ≃-refl (weigh-· ks c d))
            (interchange s t (weigh ks c) (weigh ks d))

  paired-mono : ∀ {n} (ks : Vec ℕ n) {c d : Vec C n} {s t : C}
              → c ≾ᵛ d → s ≾ t → paired ks c s ≾ paired ks d t
  paired-mono ks p q = ≾-trans (·-monoˡ-≾ q) (·-monoʳ-≾ (weigh-mono ks p))

  -- the greatest grade, where `G`'s greatest grade absorbs

  paired-⊤ : (∀ a → ⊤ · a ≡ ⊤) → ∀ {n} (ks : Vec ℕ n) → paired ks ⊤ᵛ ⊤ ≡ ⊤
  paired-⊤ absorb ks = absorb (weigh ks ⊤ᵛ)

------------------------------------------------------------------------
-- The two instances

open import Grades.Examples.Time.UpperBound using (·ₒ-comm; [0,_]; ∞)
open import Grades.Examples.Time.LowerBound using () renaming (·ₒ-comm to ·ₗ-comm)

module WeighUpper = Weigh upper-bound
                      (λ a b → Grade.≃-reflexive upper-bound (·ₒ-comm a b))
module WeighLower  = Weigh lower-bound
                      (λ a b → Grade.≃-reflexive lower-bound (·ₗ-comm a b))

-- the deadline's greatest grade absorbs

paired-⊤ʳ : ∀ {n} (ks : Vec ℕ n) → WeighUpper.paired ks (Power.⊤ᵛ upper-bound) [0, ∞ ] ≡ [0, ∞ ]
paired-⊤ʳ = WeighUpper.paired-⊤ absorb
  where
    absorb : ∀ a → _ ≡ [0, ∞ ]
    absorb [0, _ ] = refl

-- the lower bound's greatest grade is the unit, and so is its every
-- counter

paired-⊤ˡ : ∀ {n} (ks : Vec ℕ n)
          → Grade._≃_ lower-bound
              (WeighLower.paired ks (Power.⊤ᵛ lower-bound) (Grade.⊤ lower-bound))
              (Grade.⊤ lower-bound)
paired-⊤ˡ ks = WeighLower.paired-𝟏 ks
