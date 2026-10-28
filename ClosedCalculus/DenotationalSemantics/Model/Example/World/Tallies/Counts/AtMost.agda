------------------------------------------------------------------------
-- A tally Kripke frame for at-most counts.                           --
--                                                                    --
-- A world is a tally, how often each of the `n` counters has been    --
-- drawn on. A quota `ks` reaches the tallies that rise on each       --
-- counter by at most its bound, `unlimited` bounding nothing:        --
--                                                                    --
--   ws ⊑[ ks ] ws'   iff   wᵢ ≤ w'ᵢ   and   ↑ w'ᵢ ≤∞ ↑ wᵢ +∞ kᵢ      --
--                                          for every counter i       --
--                                                                    --
-- It is the power of the right-sided tick frame, which moves only    --
-- forward: the unit is least, so without `wᵢ ≤ w'ᵢ` the unit grade   --
-- would lower a tally.                                               --
------------------------------------------------------------------------

module ClosedCalculus.DenotationalSemantics.Model.Example.World.Tallies.Counts.AtMost where

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Product using (_×_)
open import Data.Unit using () renaming (⊤ to 𝟙)
open import Data.Vec.Base using ([]; _∷_)

open import Grades.Examples.Time.RightSided
  using (right-sided-intervals; [0,_]; ↑_; _+∞_; _≤∞_)
open import Grades.Examples.Counts.AtMost using (at-most-counts)

open import Util.Equality

open import ClosedCalculus.DenotationalSemantics.Model.World
open import ClosedCalculus.DenotationalSemantics.Model.Example.World.Tallies.Counts.Power
  right-sided-intervals using (_^_)

import ClosedCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided as RS

-- The frame: one right-sided tick frame per counter.

tallies : (n : ℕ) → World (at-most-counts n)
tallies n = RS.ticks ^ n

-- the relation it states, at one counter

⊑-def : ∀ {w k w'}
      → World._⊑[_]_ (tallies 1) (w ∷ []) ([0, k ] ∷ []) (w' ∷ [])
      ≡ (((w ≤ w') × (↑ w' ≤∞ (↑ w +∞ k))) × 𝟙)
⊑-def = refl
