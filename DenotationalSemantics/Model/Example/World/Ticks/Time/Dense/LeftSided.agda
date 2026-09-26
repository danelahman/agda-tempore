------------------------------------------------------------------------
-- A time-ticks Kripke frame for the left-sided intervals of dense    --
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

module DenotationalSemantics.Model.Example.World.Ticks.Time.Dense.LeftSided where

open import Syntax.Grades.Example.Time.Dense.LeftSided
  using (ℚ≥0; [_,+∞⟩; _+_; _≤_; dense-left-sided-intervals)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Reindex using (reindexʷ)
open import DenotationalSemantics.Model.World.Action using (action)

-- The frame.

ticks : World dense-left-sided-intervals
ticks = reindexʷ (action dense-left-sided-intervals) [_,+∞⟩

open World ticks public using () renaming (_⊑[_]_ to _⊑ᵗ[_]_)

-- the relation it states

⊑ᵗ-def : ∀ {w q w'} → (w ⊑ᵗ[ [ q ,+∞⟩ ] w') ≡ (w + q ≤ w')
⊑ᵗ-def = refl
