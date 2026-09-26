------------------------------------------------------------------------
-- A time-ticks Kripke frame for the two-sided intervals of dense     --
-- time, with a possibly-infinite right endpoint.                     --
--                                                                    --
-- Worlds are time points `ℚ≥0`. A grade `[ p , a ]` reaches exactly  --
-- the worlds inside its window ahead:                                --
--                                                                    --
--   w ⊑ᵗ[ [ p , a ] ] w'   iff   w + p ≤ w'   and   ↑ w' ≤∞ ↑ w +∞ a --
--                                                                    --
-- It is the action frame of the grade at the degenerate intervals    --
-- `[ q , ↑ q ]`. The lower bound keeps every move forward.           --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Ticks.Time.Dense.TwoSided where

open import Data.Product using (_×_)

open import Relation.Nullary.Decidable using (fromWitness)

open import Syntax.Grades.Example.Time.Dense.TwoSided
  using (ℚ≥0; Interval∞; [_,_]; ↑_; _+_; _+∞_; _≤_; _≤∞_; ≤∞-refl;
         dense-two-sided-intervals-with-∞)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Reindex using (reindexʷ)
open import DenotationalSemantics.Model.World.Action using (action)

-- a time point, as the interval that is just it

point : ℚ≥0 → Interval∞
point q = [ q , ↑ q ] {fromWitness ≤∞-refl}

-- The frame.

ticks : World dense-two-sided-intervals-with-∞
ticks = reindexʷ (action dense-two-sided-intervals-with-∞) point

open World ticks public using () renaming (_⊑[_]_ to _⊑ᵗ[_]_)

-- the relation it states

⊑ᵗ-def : ∀ {w p a w'} {p≤a}
       → (w ⊑ᵗ[ [ p , a ] {p≤a} ] w') ≡ ((w + p ≤ w') × (↑ w' ≤∞ (↑ w +∞ a)))
⊑ᵗ-def = refl
