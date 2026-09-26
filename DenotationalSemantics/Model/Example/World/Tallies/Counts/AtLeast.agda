------------------------------------------------------------------------
-- A tally Kripke frame for at-least counts.                          --
--                                                                    --
-- A world is a tally, how often each of the `n` counters has been    --
-- drawn on. A guarantee `ks` reaches the tallies that rise on each   --
-- counter by at least its bound:                                     --
--                                                                    --
--   ws ⊑[ ks ] ws'   iff   kᵢ + wᵢ ≤ w'ᵢ   for every counter i       --
--                                                                    --
-- It is the power of the left-sided tick frame, whose lower bound    --
-- keeps every move forward.                                          --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Tallies.Counts.AtLeast where

open import Data.Nat.Base using (ℕ; _+_; _≤_)
open import Data.Product using (_×_)
open import Data.Unit using () renaming (⊤ to 𝟙)
open import Data.Vec.Base using ([]; _∷_)

open import Syntax.Grades.Example.Time.LeftSided
  using (left-sided-intervals; [_,+∞⟩)
open import Syntax.Grades.Example.Counts.AtLeast using (at-least-counts)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.Example.World.Tallies.Counts.Power
  left-sided-intervals using (_^_)

import DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSided as LS

-- The frame.

tallies : (n : ℕ) → World (at-least-counts n)
tallies n = LS.ticks ^ n

-- the relation it states, at one counter

⊑-def : ∀ {w k w'}
      → World._⊑[_]_ (tallies 1) (w ∷ []) ([ k ,+∞⟩ ∷ []) (w' ∷ [])
      ≡ ((k + w ≤ w') × 𝟙)
⊑-def = refl
