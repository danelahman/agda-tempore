-------------------------------------------------------------------------
-- A time-ticks Kripke frame for the upper bounds of dense             --
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

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.Rational.UpperBound where

open import Data.Product using (_×_)

open import Grades.Examples.Time.Rational.UpperBound
  using (ℚ≥0; [0,_]; ↑_; _+∞_; _≤∞_; _≤_; ≤-refl; ≤-trans; ≤-irrelevant;
         rational-upper-bounds)

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Reindex using (reindexʷ)
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Action using (action; forward)

-- The frame.

ticks : World rational-upper-bounds
ticks = forward (reindexʷ (action rational-upper-bounds) (λ p → [0, ↑ p ]))
                _≤_ ≤-refl ≤-trans ≤-irrelevant

open World ticks public using () renaming (_⊑[_]_ to _⊑ᵗ[_]_)

-- the relation it states

⊑ᵗ-def : ∀ {w a w'} → (w ⊑ᵗ[ [0, a ] ] w') ≡ ((w ≤ w') × (↑ w' ≤∞ (↑ w +∞ a)))
⊑ᵗ-def = refl
