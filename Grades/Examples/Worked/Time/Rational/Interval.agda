------------------------------------------------------------------------
-- Worked instances of the dense interval grade.                      --
--                                                                    --
-- "Between `min` and `max` units", ordered by containment: orderings --
-- between concrete grades, each established by the decision          --
-- procedure of the grade; the join, sequencing, and the discrete     --
-- windows read in rational time.                                     --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Rational.Interval where

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade; GradeMorphism)

open import Util.Equality

import Grades.Examples.Time.Rational.Interval as T

import Grades.Examples.Time.Rational.IntervalClosed as Closed
import Grades.Examples.Time.Interval as Discrete

open import Grades.Examples.Time.Rational.ExtendedRational
  using (↑_; ∞; _/_; #_; nonZero)

open import Grades.Examples.Worked.Time.Rational.Decide using (module Decide)

open Decide T.rational-interval renaming (≾! to ≾²!; ⋠! to ⋠²!)

------------------------------------------------------------------------
-- Interval: "between min and max units"
--
-- The order is containment: a wider window is weaker.

interval-weaken : T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1 / 2 , ↑ 5 / 2 ]
interval-weaken = ≾²!

interval-no-strengthen : ¬ (T.[ 1 / 2 , ↑ 5 / 2 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ])
interval-no-strengthen = ⋠²!

-- overlapping windows are incomparable

interval-incomparable₁ : ¬ (T.[ 1 / 2 , ↑ # 1 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ])
interval-incomparable₁ = ⋠²!

interval-incomparable₂ : ¬ (T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1 / 2 , ↑ # 1 ])
interval-incomparable₂ = ⋠²!

-- and their join is the smallest window containing both

interval-join : T.[ 1 / 2 , ↑ # 1 ] T.⊔ᵢ T.[ # 1 , ↑ # 2 ] ≡ T.[ 1 / 2 , ↑ # 2 ]
interval-join = refl

-- a half-unit delay followed by a task of 1 to 2 units

interval-seq : T.[ 1 / 2 , ↑ 1 / 2 ] T.·ᵢ T.[ # 1 , ↑ # 2 ] ≡ T.[ 3 / 2 , ↑ 5 / 2 ]
interval-seq = refl

-- a delay by one unit is two half-unit delays

interval-tick : Grade.ι T.rational-interval (# 1)
         ≡ T.[ 1 / 2 , ↑ 1 / 2 ] T.·ᵢ T.[ 1 / 2 , ↑ 1 / 2 ]
interval-tick = refl

------------------------------------------------------------------------
-- The time intervals in whole steps, read in rational time

interval-embed : GradeMorphism.map T.interval→rational Discrete.[ 1 , Discrete.↑ 2 ]
          ≡ T.[ # 1 , ↑ # 2 ]
interval-embed = refl

interval-embed-∞ : GradeMorphism.map T.interval→rational Discrete.[ 3 , Discrete.∞ ]
            ≡ T.[ # 3 , ∞ ]
interval-embed-∞ = refl

-- a dense window strictly inside the image of a discrete one

interval-inside : T.[ 1 / 2 , ↑ 3 / 2 ]
               T.≾ᵢ GradeMorphism.map T.interval→rational Discrete.[ 0 , Discrete.↑ 2 ]
interval-inside = ≾²!

------------------------------------------------------------------------
-- Open ends

-- an open end is a smaller interval than the closed one at the same
-- point, and not the other way round

interval-open-inside : T.] # 1 , ↑ # 2 ] T.≾ᵢ T.[ # 1 , ↑ # 2 ]
interval-open-inside = ≾²!

interval-open-not-outside : ¬ (T.[ # 1 , ↑ # 2 ] T.≾ᵢ T.] # 1 , ↑ # 2 ])
interval-open-not-outside = ⋠²!

-- and a closed interval with a higher lower end does not contain it

interval-open-not-closed : ¬ (T.] # 1 , ↑ # 2 ] T.≾ᵢ T.[ 1001 / 1000 , ↑ # 2 ])
interval-open-not-closed = ⋠²!

-- an end of a sum is open when an end summed is

interval-open-seq : T.] # 0 , ↑ # 1 [ T.·ᵢ T.[ 1 / 2 , ↑ # 1 ] ≡ T.] 1 / 2 , ↑ # 2 [
interval-open-seq = refl

interval-closed-seq : T.[ # 1 , ↑ # 2 ] T.·ᵢ T.[ # 1 , ↑ # 1 ] ≡ T.[ # 2 , ↑ # 3 ]
interval-closed-seq = refl

-- the join of two half-open windows meeting at a point is the closed
-- window around both

interval-open-join : T.[ # 0 , ↑ # 1 [ T.⊔ᵢ T.] # 1 , ↑ # 2 ] ≡ T.[ # 0 , ↑ # 2 ]
interval-open-join = refl

-- without an upper bound, the open and closed ends are the same grade

interval-open-∞ : T.[ # 3 , ∞ [ ≡ T.[ # 3 , ∞ ]
interval-open-∞ = refl

------------------------------------------------------------------------
-- The closed intervals, as a sub-grade

interval-closed : GradeMorphism.map T.closed→interval Closed.[ 1 / 2 , ↑ # 2 ]
           ≡ T.[ 1 / 2 , ↑ # 2 ]
interval-closed = refl
