------------------------------------------------------------------------
-- Worked instances of the grade systems over left-sided time paired  --
-- with a security level.                                             --
--                                                                    --
-- The report under each system: a run of 45 steps that reads `High`  --
-- data distinguishes timed declassification, an embargo alone and a  --
-- taint check alone.                                                 --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Product.LeftSidedTimeLevel where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade; GradeSystem; _→ᵍ_)
open import Syntax.Grades.Example.Time.LeftSided using ([_,+∞⟩; left-sided-intervals)
open import Syntax.Grades.Example.SecurityLevel using (High; Low; two-point-levels)
open import Syntax.Grades.Example.Product.LeftSidedTimeLevel
  using (left-sided-time×low-high)
open import Syntax.Grades.Example.System.Product.LeftSidedTimeLevel
  using (embargo-and-taint; embargo; taint)

open import Util.Equality

------------------------------------------------------------------------
-- The report under each system
--
-- `unbox` asks that the image of what ran since boxing be `≾` the box's
-- grade. A run of 45 steps that read `High` data is the witness that
-- the systems differ.

module Checked (G : Grade) where

  open Grade G

  ≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
  ≾! _ _ {p} = toWitness p

  ⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! _ _ {p} = toWitnessFalse p

open _→ᵍ_ using (map)

tainted-run : Grade.Carrier left-sided-time×low-high
tainted-run = ([ 45 ,+∞⟩ , High)

-- embargo and taint check: the tainted run may not publish

module _ where
  open Grade left-sided-time×low-high
  open Checked left-sided-time×low-high

  withheld : ¬ (map (GradeSystem.∣ embargo-and-taint ∣ᵉ) tainted-run
                  ≾ ([ 30 ,+∞⟩ , Low))
  withheld = ⋠! tainted-run ([ 30 ,+∞⟩ , Low)

-- embargo only: the taint is forgotten, and the run may publish

module _ where
  open Grade left-sided-intervals
  open Checked left-sided-intervals

  forgets-taint : map (GradeSystem.∣ embargo ∣ᵉ) tainted-run ≡ [ 45 ,+∞⟩
  forgets-taint = refl

  published : map (GradeSystem.∣ embargo ∣ᵉ) tainted-run ≾ [ 30 ,+∞⟩
  published = ≾! [ 45 ,+∞⟩ [ 30 ,+∞⟩

-- taint check only: the run is refused whatever the time

module _ where
  open Grade two-point-levels
  open Checked two-point-levels

  refused : ¬ (map (GradeSystem.∣ taint ∣ᵉ) tainted-run ≾ Low)
  refused = ⋠! High Low
