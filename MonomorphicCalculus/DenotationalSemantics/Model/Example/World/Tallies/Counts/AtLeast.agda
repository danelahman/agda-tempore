------------------------------------------------------------------------
-- A tally Kripke frame for at-least counts.                          --
--                                                                    --
-- A world is a tally, how often each of the `n` counters has been    --
-- drawn on. A guarantee `ks` reaches the tallies that rise on each   --
-- counter by at least its bound:                                     --
--                                                                    --
--   ws ⊑[ ks ] ws'   iff   kᵢ + wᵢ ≤ w'ᵢ   for every counter i       --
--                                                                    --
-- It is the power of the lower-bound tick frame, whose lower bound   --
-- keeps every move forward.                                          --
------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Tallies.Counts.AtLeast where

open import Data.Nat.Base using (ℕ; _+_; _≤_)
open import Data.Product using (_×_)
open import Data.Unit using () renaming (⊤ to 𝟙)
open import Data.Vec.Base using ([]; _∷_)

open import Grades.Examples.Time.LowerBound
  using (lower-bound; [_,+∞⟩)
open import Grades.Examples.Counts.AtLeast using (at-least-counts)

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Tallies.Counts.Power
  lower-bound using (_^_)

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.LowerBound as LS

-- The frame.

tallies : (n : ℕ) → World (at-least-counts n)
tallies n = LS.ticks ^ n

-- the relation it states, at one counter

⊑-def : ∀ {w k w'}
      → World._⊑[_]_ (tallies 1) (w ∷ []) ([ k ,+∞⟩ ∷ []) (w' ∷ [])
      ≡ ((k + w ≤ w') × 𝟙)
⊑-def = refl
