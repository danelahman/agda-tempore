------------------------------------------------------------------------
-- Worked instances of the grade systems over lower bounds on time    --
-- paired with a lattice.                                             --
--                                                                    --
-- The report under each system: a run of 45 steps that reads `High`  --
-- data distinguishes timed declassification, an embargo alone and a  --
-- taint check alone.                                                 --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Product.TimeLowerBoundLattice where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Durations using (Duration)
open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade; GradeSystem; _→ᵍ_)
open import Grades.Examples.Time.LowerBound using ([_,+∞⟩; lower-bound)
open import Grades.Examples.Lattice using (High; Low; low-high)
open import Grades.Examples.Product.TimeLowerBoundLattice
  using (time-lower-bound×low-high)
open import Grades.Examples.System.Product.TimeLowerBoundLattice
  using (embargo-and-taint; embargo; taint)

open import Util.Equality

------------------------------------------------------------------------
-- The report under each system
--
-- `unbox` asks that the image of what ran since boxing be `≾` the box's
-- grade. A run of 45 steps that read `High` data is the witness that
-- the systems differ.

module Checked {D : Duration} (G : Grade D) where

  open Grade G

  ≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
  ≾! _ _ {p} = toWitness p

  ⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! _ _ {p} = toWitnessFalse p

open _→ᵍ_ using (map)

tainted-run : Grade.Carrier time-lower-bound×low-high
tainted-run = ([ 45 ,+∞⟩ , High)

-- embargo and taint check: the tainted run may not publish

module _ where
  open Grade time-lower-bound×low-high
  open Checked time-lower-bound×low-high

  withheld : ¬ (map (GradeSystem.∣-∣ᵉ embargo-and-taint) tainted-run
                  ≾ ([ 30 ,+∞⟩ , Low))
  withheld = ⋠! tainted-run ([ 30 ,+∞⟩ , Low)

-- embargo only: the taint is forgotten, and the run may publish

module _ where
  open Grade lower-bound
  open Checked lower-bound

  forgets-taint : map (GradeSystem.∣-∣ᵉ embargo) tainted-run ≡ [ 45 ,+∞⟩
  forgets-taint = refl

  published : map (GradeSystem.∣-∣ᵉ embargo) tainted-run ≾ [ 30 ,+∞⟩
  published = ≾! [ 45 ,+∞⟩ [ 30 ,+∞⟩

-- taint check only: the run is refused whatever the time

module _ where
  open Grade (low-high {ℕᴰ})
  open Checked (low-high {ℕᴰ})

  refused : ¬ (map (GradeSystem.∣-∣ᵉ taint) tainted-run ≾ Low)
  refused = ⋠! High Low
