------------------------------------------------------------------------
-- A tally Kripke frame for at-most counts.                            --
--                                                                     --
-- A world is a tally, how often each of the `n` counters has been     --
-- drawn on. A quota `ks` reaches the tallies that rise on each        --
-- counter by at most its bound, `unlimited` bounding nothing:         --
--                                                                     --
--   ws ⊑[ ks ] ws'   iff   wᵢ ≤ w'ᵢ   and   ↑ w'ᵢ ≤∞ ↑ wᵢ +∞ kᵢ       --
--                                          for every counter i       --
--                                                                     --
-- It is the power of the right-sided tick frame restricted to forward --
-- moves: the unit is least, so without `wᵢ ≤ w'ᵢ` the unit grade      --
-- would lower a tally.                                                --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Tallies.Counts.AtMost where

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Product using (_×_)
open import Data.Unit using () renaming (⊤ to 𝟙)
open import Data.Vec.Base using ([]; _∷_)

open import Syntax.Grades.Example.Time.RightSided
  using (right-sided-intervals; [0,_]; ↑_; _+∞_; _≤∞_)
open import Syntax.Grades.Example.Counts.AtMost using (at-most-counts)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Action using (forward)
open import DenotationalSemantics.Model.Example.World.Tallies.Counts.Power
  right-sided-intervals using (_^_)

import DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided as RS

-- one counter: the right-sided tick frame, forward moves only

counter : World right-sided-intervals
counter = forward RS.ticks _≤_ ≤-refl ≤-trans ≤-irrelevant

-- The frame.

tallies : (n : ℕ) → World (at-most-counts n)
tallies n = counter ^ n

-- the relation it states, at one counter

⊑-def : ∀ {w k w'}
      → World._⊑[_]_ (tallies 1) (w ∷ []) ([0, k ] ∷ []) (w' ∷ [])
      ≡ (((w ≤ w') × (↑ w' ≤∞ (↑ w +∞ k))) × 𝟙)
⊑-def = refl
