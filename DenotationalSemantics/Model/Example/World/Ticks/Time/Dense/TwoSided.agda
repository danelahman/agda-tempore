------------------------------------------------------------------------
-- A time-ticks Kripke frame for the two-sided intervals of dense     --
-- time, each end open or closed and the right one possibly absent.   --
--                                                                    --
-- Worlds are time points `ℚ≥0`. A grade `i` reaches exactly the      --
-- worlds ahead by a duration it admits:                              --
--                                                                    --
--   w ⊑ᵗ[ i ] w'   iff   w' = w + τ   for some   τ ∈ⁱ i              --
--                                                                    --
-- It is the action frame of the grade at the points `[ q , ↑ q ]`.   --
-- The relation it states is that `w'` lies in the interval `i`       --
-- shifted by `w` (`⊑ᵗ-def`), which is the reading above because the  --
-- sum of intervals is their Minkowski sum (`⊑ᵗ-sound`,               --
-- `⊑ᵗ-complete`). The lower end keeps every move forward.            --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.Time.Dense.TwoSided where

open import Data.Product using (Σ; _×_)
open import Relation.Nullary.Decidable using (toWitnessFalse)

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᵀ; ℚ≥0-dense)
open import Syntax.Grades.Example.Time.Dense.NonNegativeRational
  using (ℚ≥0; _+_; 0ᵈ; 1ᵈ; _≤?_)
open import Syntax.Grades.Example.Time.Dense.TwoSided
  using (pointⁱ; _⊕_; dense-two-sided-intervals-with-∞)
open import Syntax.Durations.Intervals.Dense ℚ≥0ᵀ
  using (_∈ⁱ_; shift-∈; module Exact)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Reindex using (reindexʷ)
open import DenotationalSemantics.Model.World.Action using (action)

-- The frame.

ticks : World dense-two-sided-intervals-with-∞
ticks = reindexʷ (action dense-two-sided-intervals-with-∞) pointⁱ

open World ticks public using () renaming (_⊑[_]_ to _⊑ᵗ[_]_)

-- the relation it states

⊑ᵗ-def : ∀ {w i w'} → (w ⊑ᵗ[ i ] w') ≡ (w' ∈ⁱ (pointⁱ w ⊕ i))
⊑ᵗ-def = refl

-- and what that says: `w'` is `w` moved on by a duration `i` admits

⊑ᵗ-sound : ∀ {w i τ} → τ ∈ⁱ i → w ⊑ᵗ[ i ] (w + τ)
⊑ᵗ-sound {w} {i} = shift-∈ {w} {i}

⊑ᵗ-complete : ∀ {w i w'} → w ⊑ᵗ[ i ] w' → Σ ℚ≥0 (λ τ → τ ∈ⁱ i × w + τ ≡ w')
⊑ᵗ-complete {w} {i} =
  Exact.∈-shift ℚ≥0-dense 1ᵈ (toWitnessFalse {a? = 1ᵈ ≤? 0ᵈ} _) {w} {i}
