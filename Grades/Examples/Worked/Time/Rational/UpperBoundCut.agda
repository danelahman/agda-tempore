------------------------------------------------------------------------
-- Worked instances of the dense upper-bound grade with open or       --
-- closed ends.                                                       --
--                                                                    --
-- "At most `a` units", "less than `a` units" and no bound: orderings --
-- between concrete grades, each established by the decision          --
-- procedure of the grade; sequencing, the join, the zero-product law --
-- and the morphisms into the grade, computed.                        --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Rational.UpperBoundCut where

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade; GradeMorphism)

open import Util.Equality

import Grades.Examples.Time.Rational.UpperBoundCut as R

import Grades.Examples.Time.Rational.UpperBound as Closed
import Grades.Examples.Time.Rational.Interval as T
import Grades.Examples.Time.UpperBound as Discrete

open import Grades.Examples.Time.Rational.ExtendedRational
  using (↑_; ∞; _/_; #_; nonZero)

open import Grades.Examples.Worked.Time.Rational.Decide using (module Decide)

open Decide R.rational-upper-bound-cuts renaming (≾! to ≾ʳ!; ⋠! to ⋠ʳ!)

G = R.rational-upper-bound-cuts

------------------------------------------------------------------------
-- The order: containment of the durations admitted

-- "less than 2" is stronger than "at most 2", and not the other way
-- round

rci-open-below : R.< # 2 R.≾ᵘ R.≤ ↑ # 2
rci-open-below = ≾ʳ!

rci-closed-not-below : ¬ (R.≤ ↑ # 2 R.≾ᵘ R.< # 2)
rci-closed-not-below = ⋠ʳ!

-- a smaller bound is stronger, open or closed

rci-smaller : R.≤ ↑ 1999 / 1000 R.≾ᵘ R.< # 2
rci-smaller = ≾ʳ!

rci-larger-not-below : ¬ (R.< 5 / 2 R.≾ᵘ R.≤ ↑ # 2)
rci-larger-not-below = ⋠ʳ!

-- every bound is below none, and no bound is below a finite one

rci-top : R.≤ ↑ # 2 R.≾ᵘ R.≤ ∞
rci-top = ≾ʳ! {R.≤ ↑ # 2} {R.≤ ∞}

rci-top-not-below : ¬ (R.≤ ∞ R.≾ᵘ R.≤ ↑ # 1000)
rci-top-not-below = ⋠ʳ! {R.≤ ∞} {R.≤ ↑ # 1000}

------------------------------------------------------------------------
-- Sequencing adds the bounds, strict when a bound summed is, and no
-- bound absorbs

rci-seq-open : R.< # 2 R.·ᵘ R.≤ ↑ # 3 ≡ R.< # 5
rci-seq-open = refl

rci-seq-closed : R.≤ ↑ 1 / 2 R.·ᵘ R.≤ ↑ 2 / 3 ≡ R.≤ ↑ 7 / 6
rci-seq-closed = refl

rci-seq-∞ : R.≤ ↑ # 2 R.·ᵘ R.≤ ∞ ≡ R.≤ ∞
rci-seq-∞ = refl

-- a delay by one unit is two half-unit delays

rci-tick : Grade.ι G (# 1) ≡ Grade.ι G (1 / 2) R.·ᵘ Grade.ι G (1 / 2)
rci-tick = refl

------------------------------------------------------------------------
-- The join is the weaker bound

rci-join-side : R.< # 2 R.⊔ᵘ R.≤ ↑ # 2 ≡ R.≤ ↑ # 2
rci-join-side = refl

rci-join-point : R.< # 1 R.⊔ᵘ R.< # 2 ≡ R.< # 2
rci-join-point = refl

rci-join-∞ : R.< # 1 R.⊔ᵘ R.≤ ∞ ≡ R.≤ ∞
rci-join-∞ = refl

------------------------------------------------------------------------
-- The unit "at most 0" is the least grade, and the zero-product law

rci-unit-least : Grade.𝟏 G R.≾ᵘ R.< 1 / 2
rci-unit-least = ≾ʳ!

rci-zero-product : R.≤ ↑ # 0 R.·ᵘ R.≤ ↑ # 0 R.≾ᵘ Grade.𝟏 G
rci-zero-product = ≾ʳ!

rci-zero-product-factor : R.≤ ↑ # 0 R.≾ᵘ Grade.𝟏 G
rci-zero-product-factor =
  Grade.≾-zero-productʳ G {R.≤ ↑ # 0} {R.≤ ↑ # 0} rci-zero-product

-- a product with a positive factor is not within the unit, and
-- neither is the factor

rci-not-zero-product : ¬ (R.≤ ↑ # 0 R.·ᵘ R.< 1 / 2 R.≾ᵘ Grade.𝟏 G)
rci-not-zero-product = ⋠ʳ!

rci-not-zero-factor : ¬ (R.< 1 / 2 R.≾ᵘ Grade.𝟏 G)
rci-not-zero-factor = ⋠ʳ!

------------------------------------------------------------------------
-- The morphisms into the grade

rci-closed : GradeMorphism.map R.closed→cut Closed.[0, ↑ 5 / 2 ] ≡ R.≤ ↑ 5 / 2
rci-closed = refl

rci-closed-∞ : GradeMorphism.map R.closed→cut Closed.[0, ∞ ] ≡ R.≤ ∞
rci-closed-∞ = refl

rci-interval : GradeMorphism.map R.interval→cut T.] # 1 , ↑ # 2 [ ≡ R.< # 2
rci-interval = refl

rci-discrete : GradeMorphism.map R.upper-bound→rational-cut Discrete.[0, Discrete.↑ 3 ]
             ≡ R.≤ ↑ # 3
rci-discrete = refl
