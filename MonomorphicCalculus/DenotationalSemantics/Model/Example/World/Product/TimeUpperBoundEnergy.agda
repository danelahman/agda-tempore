------------------------------------------------------------------------
-- A Kripke frame for upper bounds on time paired with an energy      --
-- budget.                                                            --
--                                                                    --
-- A world is a time point and the energy spent so far. A grade       --
-- `([0, n ] , [0, e ])` reaches the worlds at most `n` ticks ahead   --
-- with at most `e` more units spent, neither going back:             --
--                                                                    --
--   (w , s) ⊑[ ([0, n ] , [0, e ]) ] (w' , s')                       --
--     iff   w ≤ w' ,  ↑ w' ≤∞ ↑ w +∞ n ,  s ≤ s' ,  ↑ s' ≤∞ ↑ s +∞ e --
--                                                                    --
-- The energy frame is the upper-bound tick frame reindexed along     --
-- the identity. The identity is not a grade morphism, `energy` not   --
-- counting time steps, but it is a lax monoid map, and a frame never --
-- sees `ι`.                                                          --
------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Product.TimeUpperBoundEnergy where

open import Data.Nat.Base using (_≤_)
open import Data.Product using (_×_; _,_)

open import Grades.Base using (Grade)
open import Grades.Examples.Time.UpperBound
  using (upper-bounds; [0,_]; ↑_; _+∞_; _≤∞_; _·ₒ_)
open import Grades.Examples.Product.TimeUpperBoundEnergy
  using (energy; time-upper-bound×energy)

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Product using (_⊗_)
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Reindex using (LaxMap; reindexᵍ)

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.UpperBound as RS

open Grade upper-bounds using (≾-refl)

-- energy: the upper-bound tick frame, along the identity

energy→time : LaxMap energy upper-bounds
energy→time = record
  { map      = λ c → c
  ; monotone = λ r → r
  ; lax-𝟏    = ≾-refl
  ; lax-·    = λ {a} {b} → ≾-refl {a ·ₒ b}
  }

spending : World energy
spending = reindexᵍ energy→time RS.ticks

-- The frame.

ticks×spending : World time-upper-bound×energy
ticks×spending = RS.ticks ⊗ spending

-- the relation it states

⊑-def : ∀ {w s n e w' s'}
      → World._⊑[_]_ ticks×spending (w , s) ([0, n ] , [0, e ]) (w' , s')
      ≡ (((w ≤ w') × (↑ w' ≤∞ (↑ w +∞ n))) × ((s ≤ s') × (↑ s' ≤∞ (↑ s +∞ e))))
⊑-def = refl
