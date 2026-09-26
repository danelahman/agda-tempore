------------------------------------------------------------------------
-- Counts and time: why no count grade projects onto time, and what a  --
-- cost model preserves when time is paired with the counts.           --
--                                                                     --
-- No projection from counts to time. In a count grade `n` time steps  --
-- are the unit, for every `n`, so `of-nat 1` and `of-nat 0` coincide; --
-- a time grade tells them apart, so no morphism preserves `of-nat`,  --
-- whatever it does otherwise.                                         --
--                                                                     --
-- A cost model `ks` weighs the counters, and `weigh ks` sums the      --
-- weighted counts in `G`, each counter's bound taken `k` times over.  --
-- With time paired alongside, as `counts ×ᵍ time` with                --
--                                                                     --
--   (c , t)  ↦  t · weigh ks c                                        --
--                                                                     --
-- the unit, the product, monotonicity, the inclusion of ℕ and the     --
-- greatest grade are all preserved (the last where `G`'s top absorbs, --
-- or is the unit). The join is not: the counts' join is pointwise, so --
-- it can combine the worst case of one counter from one run with that --
-- of another from a different run, and the weighted sum of that       --
-- exceeds both runs' weights. `Counts.Worked` exhibits the failure;   --
-- `weigh` is merely lax there, the join of the images lying below the --
-- image of the join.                                                  --
------------------------------------------------------------------------

open import Syntax.Grades

module Syntax.Grades.Example.System.Counts.Time where

open import Algebra.Definitions using (Commutative)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)

open import Util.Equality

import Syntax.Grades.Example.Counts.Power as Power

------------------------------------------------------------------------
-- No projection onto a grade that counts time

module _ (G H : Grade) where

  open Power G using (power)

  no-projection : ∀ {n} → ¬ (Grade.of-nat H 1 ≡ Grade.of-nat H 0)
                → ¬ (power n →ᵍ H)
  no-projection ne F = ne (trans (sym (map-of-nat {1})) (map-of-nat {0}))
    where open _→ᵍ_ F

-- at the two time grades the counts are built from

open import Syntax.Grades.Example.Time.RightSided
  using (right-sided-intervals)
open import Syntax.Grades.Example.Time.LeftSided
  using (left-sided-intervals)
open import Syntax.Grades.Example.Counts.AtMost using (at-most-counts)
open import Syntax.Grades.Example.Counts.AtLeast using (at-least-counts)

no-at-most-counts→right-sided-intervals :
  ∀ {n} → ¬ (at-most-counts n →ᵍ right-sided-intervals)
no-at-most-counts→right-sided-intervals =
  no-projection right-sided-intervals right-sided-intervals λ ()

no-at-least-counts→left-sided-intervals :
  ∀ {n} → ¬ (at-least-counts n →ᵍ left-sided-intervals)
no-at-least-counts→left-sided-intervals =
  no-projection left-sided-intervals left-sided-intervals λ ()

------------------------------------------------------------------------
-- Weighted sums, in a commutative grade

module Weigh (G : Grade) (comm : Commutative _≡_ (Grade._·_ G)) where

  open Grade G renaming (Carrier to C)
  open Power G using (_·ᵛ_; _⊔ᵛ_; uᵛ; ⊤ᵛ; _≾ᵛ_; ⊔ᵛ-ubˡ; ⊔ᵛ-ubʳ)

  -- `k` copies of a grade in sequence

  times : ℕ → C → C
  times zero    a = u
  times (suc k) a = a · times k a

  -- the middle-four interchange

  interchange : (a b c d : C) → (a · b) · (c · d) ≡ (a · c) · (b · d)
  interchange a b c d =
    begin
      (a · b) · (c · d)   ≡⟨ ·-assoc a b (c · d) ⟩
      a · (b · (c · d))   ≡⟨ cong (a ·_) (sym (·-assoc b c d)) ⟩
      a · ((b · c) · d)   ≡⟨ cong (λ z → a · (z · d)) (comm b c) ⟩
      a · ((c · b) · d)   ≡⟨ cong (a ·_) (·-assoc c b d) ⟩
      a · (c · (b · d))   ≡⟨ sym (·-assoc a c (b · d)) ⟩
      (a · c) · (b · d)
    ∎

  times-u : (k : ℕ) → times k u ≡ u
  times-u zero    = refl
  times-u (suc k) = trans (·-identityˡ (times k u)) (times-u k)

  times-· : (k : ℕ) (a b : C) → times k (a · b) ≡ times k a · times k b
  times-· zero    a b = sym (·-identityˡ u)
  times-· (suc k) a b =
    trans (cong ((a · b) ·_) (times-· k a b))
          (interchange a b (times k a) (times k b))

  times-mono : (k : ℕ) {a b : C} → a ≾ b → times k a ≾ times k b
  times-mono zero    p = ≾-refl
  times-mono (suc k) p = ≾-trans (·-monoˡ-≾ p) (·-monoʳ-≾ (times-mono k p))

  -- the weighted sum of a vector of counts

  weigh : ∀ {n} → Vec ℕ n → Vec C n → C
  weigh []       []       = u
  weigh (k ∷ ks) (a ∷ as) = times k a · weigh ks as

  weigh-u : ∀ {n} (ks : Vec ℕ n) → weigh ks uᵛ ≡ u
  weigh-u []       = refl
  weigh-u (k ∷ ks) = trans (cong₂ _·_ (times-u k) (weigh-u ks)) (·-identityˡ u)

  weigh-· : ∀ {n} (ks : Vec ℕ n) (c d : Vec C n)
          → weigh ks (c ·ᵛ d) ≡ weigh ks c · weigh ks d
  weigh-· []       []       []       = sym (·-identityˡ u)
  weigh-· (k ∷ ks) (a ∷ as) (b ∷ bs) =
    trans (cong₂ _·_ (times-· k a b) (weigh-· ks as bs))
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

  paired-u : ∀ {n} (ks : Vec ℕ n) → paired ks uᵛ u ≡ u
  paired-u ks = trans (cong (u ·_) (weigh-u ks)) (·-identityˡ u)

  paired-of-nat : ∀ {n} (ks : Vec ℕ n) (m : ℕ) → paired ks uᵛ (of-nat m) ≡ of-nat m
  paired-of-nat ks m = trans (cong (of-nat m ·_) (weigh-u ks)) (·-identityʳ (of-nat m))

  paired-· : ∀ {n} (ks : Vec ℕ n) (c d : Vec C n) (s t : C)
           → paired ks (c ·ᵛ d) (s · t) ≡ paired ks c s · paired ks d t
  paired-· ks c d s t =
    trans (cong ((s · t) ·_) (weigh-· ks c d))
          (interchange s t (weigh ks c) (weigh ks d))

  paired-mono : ∀ {n} (ks : Vec ℕ n) {c d : Vec C n} {s t : C}
              → c ≾ᵛ d → s ≾ t → paired ks c s ≾ paired ks d t
  paired-mono ks p q = ≾-trans (·-monoˡ-≾ q) (·-monoʳ-≾ (weigh-mono ks p))

  -- the greatest grade, where `G`'s greatest grade absorbs

  paired-⊤ : (∀ a → ⊤ · a ≡ ⊤) → ∀ {n} (ks : Vec ℕ n) → paired ks ⊤ᵛ ⊤ ≡ ⊤
  paired-⊤ absorb ks = absorb (weigh ks ⊤ᵛ)

------------------------------------------------------------------------
-- The two instances

open import Syntax.Grades.Example.Time.RightSided using (·ₒ-comm; [0,_]; ∞)
open import Syntax.Grades.Example.Time.LeftSided using () renaming (·ₒ-comm to ·ₗ-comm)

module WeighRight = Weigh right-sided-intervals ·ₒ-comm
module WeighLeft  = Weigh left-sided-intervals  ·ₗ-comm

-- the deadline's greatest grade absorbs

paired-⊤ʳ : ∀ {n} (ks : Vec ℕ n) → WeighRight.paired ks (Power.⊤ᵛ right-sided-intervals) [0, ∞ ] ≡ [0, ∞ ]
paired-⊤ʳ = WeighRight.paired-⊤ absorb
  where
    absorb : ∀ a → _ ≡ [0, ∞ ]
    absorb [0, _ ] = refl

-- the lower bound's greatest grade is the unit, and so is its every
-- counter

paired-⊤ˡ : ∀ {n} (ks : Vec ℕ n)
          → WeighLeft.paired ks (Power.⊤ᵛ left-sided-intervals) (Grade.⊤ left-sided-intervals)
          ≡ Grade.⊤ left-sided-intervals
paired-⊤ˡ ks = WeighLeft.paired-u ks
