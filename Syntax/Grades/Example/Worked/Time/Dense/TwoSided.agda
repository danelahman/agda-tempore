------------------------------------------------------------------------
-- Worked instances of the dense two-sided grade.                     --
--                                                                    --
-- "Between `min` and `max` units", ordered by containment: orderings --
-- between concrete grades, each established by the decision          --
-- procedure of the grade; the join, sequencing, and the discrete     --
-- windows read in dense time.                                        --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Time.Dense.TwoSided where

open import Relation.Nullary using (¬_)

open import Syntax.Grades using (Grade; _→ᵍ_)

open import Util.Equality

import Syntax.Grades.Example.Time.Dense.TwoSided as T

import Syntax.Grades.Example.Time.TwoSidedWithInfinity as Discrete

open import Syntax.Grades.Example.Time.Dense.ExtendedRational
  using (↑_; ∞; _/_; #_; nonZero)

open import Syntax.Grades.Example.Worked.Time.Dense.Decide using (module Decide)

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

-- one time step is two half-unit delays

tsi-tick : Grade.of-dur T.dense-two-sided-intervals-with-∞ 1
         ≡ T.[ 1 / 2 , ↑ 1 / 2 ] T.·ᵢ T.[ 1 / 2 , ↑ 1 / 2 ]
tsi-tick = refl

------------------------------------------------------------------------
-- The discrete windows, read in dense time

tsi-embed : _→ᵍ_.map T.two-sided→dense Discrete.[ 1 , Discrete.↑ 2 ]
          ≡ T.[ # 1 , ↑ # 2 ]
tsi-embed = refl

tsi-embed-∞ : _→ᵍ_.map T.two-sided→dense Discrete.[ 3 , Discrete.∞ ]
            ≡ T.[ # 3 , ∞ ]
tsi-embed-∞ = refl

-- a dense window strictly inside the image of a discrete one

tsi-inside : T.[ 1 / 2 , ↑ 3 / 2 ]
               T.≾ᵢ _→ᵍ_.map T.two-sided→dense Discrete.[ 0 , Discrete.↑ 2 ]
tsi-inside = ≾²!
