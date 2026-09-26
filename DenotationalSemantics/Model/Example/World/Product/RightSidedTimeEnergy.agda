------------------------------------------------------------------------
-- A Kripke frame for right-sided time paired with an energy budget.   --
--                                                                     --
-- A world is a time point and the energy spent so far. A grade        --
-- `([0, n ] , [0, e ])` reaches the worlds at most `n` ticks ahead    --
-- with at most `e` more units spent, neither going back:              --
--                                                                     --
--   (w , s) ⊑[ ([0, n ] , [0, e ]) ] (w' , s')                        --
--     iff   w ≤ w' ,  ↑ w' ≤∞ ↑ w +∞ n ,  s ≤ s' ,  ↑ s' ≤∞ ↑ s +∞ e  --
--                                                                     --
-- The energy frame is the forward right-sided tick frame reindexed    --
-- along the identity. The identity is not a grade morphism, `energy`  --
-- not counting time steps, but it is a lax monoid map, and a frame    --
-- never sees `of-nat`.                                                --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Product.RightSidedTimeEnergy where

open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)
open import Data.Product using (_×_; _,_)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Example.Time.RightSided
  using (right-sided-intervals; [0,_]; ↑_; _+∞_; _≤∞_; _·ₒ_)
open import Syntax.Grades.Example.Product.RightSidedTimeEnergy
  using (energy; right-sided-time×energy)

open import Util.Equality

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Product using (_⊗_)
open import DenotationalSemantics.Model.World.Reindex using (LaxMap; reindexᵍ)
open import DenotationalSemantics.Model.World.Action using (forward)

import DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided as RS

open Grade right-sided-intervals using (≾-refl)

-- time: the right-sided tick frame, forward moves only

time : World right-sided-intervals
time = forward RS.ticks _≤_ ≤-refl ≤-trans ≤-irrelevant

-- energy: the same frame, along the identity

energy→time : LaxMap energy right-sided-intervals
energy→time = record
  { map      = λ c → c
  ; monotone = λ r → r
  ; lax-u    = ≾-refl
  ; lax-·    = λ {a} {b} → ≾-refl {a ·ₒ b}
  }

spending : World energy
spending = reindexᵍ energy→time time

-- The frame.

ticks×spending : World right-sided-time×energy
ticks×spending = time ⊗ spending

-- the relation it states

⊑-def : ∀ {w s n e w' s'}
      → World._⊑[_]_ ticks×spending (w , s) ([0, n ] , [0, e ]) (w' , s')
      ≡ (((w ≤ w') × (↑ w' ≤∞ (↑ w +∞ n))) × ((s ≤ s') × (↑ s' ≤∞ (↑ s +∞ e))))
⊑-def = refl
