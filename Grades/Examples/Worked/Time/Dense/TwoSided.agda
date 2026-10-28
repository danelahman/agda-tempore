------------------------------------------------------------------------
-- Worked instances of the dense two-sided grade.                     --
--                                                                    --
-- "Between `min` and `max` units", ordered by containment: orderings --
-- between concrete grades, each established by the decision          --
-- procedure of the grade; the join, sequencing, and the discrete     --
-- windows read in dense time.                                        --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Dense.TwoSided where

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade; GradeMorphism)

open import Util.Equality

import Grades.Examples.Time.Dense.TwoSided as T

import Grades.Examples.Time.Dense.TwoSidedClosed as Closed
import Grades.Examples.Time.TwoSidedWithInfinity as Discrete

open import Grades.Examples.Time.Dense.ExtendedRational
  using (↑_; ∞; _/_; #_; nonZero)

open import Grades.Examples.Worked.Time.Dense.Decide using (module Decide)

open Decide T.dense-two-sided-intervals-with-∞ renaming (≾! to ≾²!; ⋠! to ⋠²!)

------------------------------------------------------------------------
-- Two-sided: "between min and max units"
--
-- The order is containment: a wider window is weaker.

tsi-weaken : T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1 / 2 , ↑ 5 / 2 ]
tsi-weaken = ≾²!

tsi-no-strengthen : ¬ (T.[ 1 / 2 , ↑ 5 / 2 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ])
tsi-no-strengthen = ⋠²!

-- overlapping windows are incomparable

tsi-incomparable₁ : ¬ (T.[ 1 / 2 , ↑ # 1 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ])
tsi-incomparable₁ = ⋠²!

tsi-incomparable₂ : ¬ (T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1 / 2 , ↑ # 1 ])
tsi-incomparable₂ = ⋠²!

-- and their join is the smallest window containing both

tsi-join : T.[ 1 / 2 , ↑ # 1 ] T.⊔ᵢ T.[ # 1 , ↑ # 2 ] ≡ T.[ 1 / 2 , ↑ # 2 ]
tsi-join = refl

-- a half-unit delay followed by a task of 1 to 2 units

tsi-seq : T.[ 1 / 2 , ↑ 1 / 2 ] T.·ᵢ T.[ # 1 , ↑ # 2 ] ≡ T.[ 3 / 2 , ↑ 5 / 2 ]
tsi-seq = refl

-- a delay by one unit is two half-unit delays

tsi-tick : Grade.of-dur T.dense-two-sided-intervals-with-∞ (# 1)
         ≡ T.[ 1 / 2 , ↑ 1 / 2 ] T.·ᵢ T.[ 1 / 2 , ↑ 1 / 2 ]
tsi-tick = refl

------------------------------------------------------------------------
-- The discrete windows, read in dense time

tsi-embed : GradeMorphism.map T.two-sided→dense Discrete.[ 1 , Discrete.↑ 2 ]
          ≡ T.[ # 1 , ↑ # 2 ]
tsi-embed = refl

tsi-embed-∞ : GradeMorphism.map T.two-sided→dense Discrete.[ 3 , Discrete.∞ ]
            ≡ T.[ # 3 , ∞ ]
tsi-embed-∞ = refl

-- a dense window strictly inside the image of a discrete one

tsi-inside : T.[ 1 / 2 , ↑ 3 / 2 ]
               T.≾ᵢ GradeMorphism.map T.two-sided→dense Discrete.[ 0 , Discrete.↑ 2 ]
tsi-inside = ≾²!

------------------------------------------------------------------------
-- Open ends

-- an open end is a smaller interval than the closed one at the same
-- point, and not the other way round

tsi-open-inside : T.] # 1 , ↑ # 2 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ]
tsi-open-inside = ≾²!

tsi-open-not-outside : ¬ (T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.] # 1 , ↑ # 2 ])
tsi-open-not-outside = ⋠²!

-- and a closed interval with a higher lower end does not contain it

tsi-open-not-closed : ¬ (T.] # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1001 / 1000 , ↑ # 2 ])
tsi-open-not-closed = ⋠²!

-- an end of a sum is open when an end summed is

tsi-open-seq : T.] # 0 , ↑ # 1 [ T.·ᵢ T.[ 1 / 2 , ↑ # 1 ] ≡ T.] 1 / 2 , ↑ # 2 [
tsi-open-seq = refl

tsi-closed-seq : T.[ # 1 , ↑ # 2 ] T.·ᵢ T.[ # 1 , ↑ # 1 ] ≡ T.[ # 2 , ↑ # 3 ]
tsi-closed-seq = refl

-- the join of two half-open windows meeting at a point is the closed
-- window around both

tsi-open-join : T.[ # 0 , ↑ # 1 [ T.⊔ᵢ T.] # 1 , ↑ # 2 ] ≡ T.[ # 0 , ↑ # 2 ]
tsi-open-join = refl

-- without an upper bound, the open and closed ends are the same grade

tsi-open-∞ : T.[ # 3 , ∞ [ ≡ T.[ # 3 , ∞ ]
tsi-open-∞ = refl

------------------------------------------------------------------------
-- The closed intervals, as a sub-grade

tsi-closed : GradeMorphism.map T.closed→strict Closed.[ 1 / 2 , ↑ # 2 ]
           ≡ T.[ 1 / 2 , ↑ # 2 ]
tsi-closed = refl
