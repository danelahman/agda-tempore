-------------------------------------------------------------------------
-- A time-ticks Kripke frame for the right-sided intervals of dense    --
-- time.                                                               --
--                                                                     --
-- Worlds are time points `ℚ≥0`. A grade `[0, a ]` (with `a : ℚ∞`)     --
-- reaches the worlds ahead by at most `a` time units, an infinite `a` --
-- bounding nothing:                                                   --
--                                                                     --
--   w ⊑ᵗ[ [0, a ] ] w'   iff   w ≤ w'   and   ↑ w' ≤∞ ↑ w +∞ a        --
--                                                                     --
-- It is the action frame of the grade at the points `[0, ↑ p ]`,      --
-- restricted to forward moves: the unit is least, so without `w ≤ w'` --
-- the unit grade would reach the past.                                --
-------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.Time.Dense.RightSided where

open import Data.Product using (_×_)

open import Syntax.Grades.Example.Time.Dense.RightSided
  using (ℚ≥0; [0,_]; ↑_; _+∞_; _≤∞_; _≤_; ≤-refl; ≤-trans; ≤-irrelevant;
         dense-right-sided-intervals)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Reindex using (reindexʷ)
open import DenotationalSemantics.Model.World.Action using (action; forward)

-- The frame.

ticks : World dense-right-sided-intervals
ticks = forward (reindexʷ (action dense-right-sided-intervals) (λ p → [0, ↑ p ]))
                _≤_ ≤-refl ≤-trans ≤-irrelevant

open World ticks public using () renaming (_⊑[_]_ to _⊑ᵗ[_]_)

-- the relation it states

⊑ᵗ-def : ∀ {w a w'} → (w ⊑ᵗ[ [0, a ] ] w') ≡ ((w ≤ w') × (↑ w' ≤∞ (↑ w +∞ a)))
⊑ᵗ-def = refl
