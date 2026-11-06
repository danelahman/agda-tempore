------------------------------------------------------------------------
-- Banked trace grades of dense time, and whole steps read in them.   --
--                                                                    --
-- The banked trace grades of `Example.Traces.Banked` are built over  --
-- any time domain; at `ℚ≥0ᵀ` their delays and costs are rational.    --
-- Whole steps embed: the inclusion `ℕ→ℚ≥0ᴰ` keeps positive           --
-- durations positive, so `Example.Traces.Banked.Morphism` carries    --
-- each grade over ℕ at costs `c` to the dense one at costs `# ∘ c`   --
-- (`Left.lower-bound→`, `Right.upper-bound→`, `Two.interval→`).      --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Grades.Examples.Traces.Banked.Rational
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Grades.Durations.Nat using (ℕᵀ)
open import Grades.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℕ→ℚ≥0ᴰ)
open import Util.NonNegativeRational
  using (_≤_; _≤?_; #_; 0ᵈ; 1ᵈ; +-≤0ˡ)

-- a positive number of steps is a positive duration

#-pos : (n : ℕ) → # n ≤ 0ᵈ → n ℕ.≤ 0
#-pos zero    _ = z≤n
#-pos (suc n) p = ⊥-elim (toWitnessFalse {a? = 1ᵈ ≤? 0ᵈ} _ (+-≤0ˡ {1ᵈ} {# n} p))

open import Grades.Examples.Traces.Banked.Morphism
  ℕᵀ ℚ≥0ᵀ ℕ→ℚ≥0ᴰ #-pos Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans public
