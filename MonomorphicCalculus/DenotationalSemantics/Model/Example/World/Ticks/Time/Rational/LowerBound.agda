------------------------------------------------------------------------
-- A time-ticks Kripke frame for the lower bounds of dense            --
-- time.                                                              --
--                                                                    --
-- Worlds are time points `ℚ≥0`. A grade `[ q ,+∞⟩` reaches every     --
-- world at least `q` time units ahead:                               --
--                                                                    --
--   w ⊑ᵗ[ [ q ,+∞⟩ ] w'   iff   w + q ≤ w'                           --
--                                                                    --
-- It is the action frame of the grade at the points `[ p ,+∞⟩`, so   --
-- the laws are the grade's own. The lower bound keeps every move     --
-- forward.                                                           --
------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.Rational.LowerBound where

open import Grades.Examples.Time.Rational.LowerBound
  using (ℚ≥0; [_,+∞⟩; _+_; _≤_; rational-lower-bounds)

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Reindex using (reindexʷ)
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Action using (action)

-- The frame.

ticks : World rational-lower-bounds
ticks = reindexʷ (action rational-lower-bounds) [_,+∞⟩

open World ticks public using () renaming (_⊑[_]_ to _⊑ᵗ[_]_)

-- the relation it states

⊑ᵗ-def : ∀ {w q w'} → (w ⊑ᵗ[ [ q ,+∞⟩ ] w') ≡ (w + q ≤ w')
⊑ᵗ-def = refl
