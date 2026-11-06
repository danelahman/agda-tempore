------------------------------------------------------------------------
-- Worked instances of the dense lower-bound grade with open or       --
-- closed ends.                                                       --
--                                                                    --
-- "At least `p` units" and "more than `p` units": orderings between  --
-- concrete grades, each established by the decision procedure of the --
-- grade; sequencing, the join and the morphisms into the grade,      --
-- computed.                                                          --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Rational.LowerBoundCut where

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade; GradeMorphism)

open import Util.Equality

import Grades.Examples.Time.Rational.LowerBoundCut as L

import Grades.Examples.Time.Rational.LowerBound as Closed
import Grades.Examples.Time.Rational.Interval as T
import Grades.Examples.Time.LowerBound as Discrete

open import Grades.Examples.Time.Rational.ExtendedRational
  using (↑_; _/_; #_; nonZero)

open import Grades.Examples.Worked.Time.Rational.Decide using (module Decide)

open Decide L.rational-lower-bound-cut renaming (≾! to ≾ˡ!; ⋠! to ⋠ˡ!)

G = L.rational-lower-bound-cut

------------------------------------------------------------------------
-- The order: containment of the durations admitted

-- "more than 1" is stronger than "at least 1", and not the other way
-- round

lci-open-below : L.> # 1 L.≾ˡ L.≥ # 1
lci-open-below = ≾ˡ!

lci-closed-not-below : ¬ (L.≥ # 1 L.≾ˡ L.> # 1)
lci-closed-not-below = ⋠ˡ!

-- a larger bound is stronger, open or closed

lci-larger : L.≥ 1001 / 1000 L.≾ˡ L.> # 1
lci-larger = ≾ˡ!

lci-smaller-not-below : ¬ (L.> 1 / 2 L.≾ˡ L.≥ # 1)
lci-smaller-not-below = ⋠ˡ!

------------------------------------------------------------------------
-- Sequencing adds the bounds, strict when a bound summed is

lci-seq-open : L.≥ # 1 L.·ˡ L.> # 2 ≡ L.> # 3
lci-seq-open = refl

lci-seq-closed : L.≥ 1 / 2 L.·ˡ L.≥ 1 / 2 ≡ L.≥ # 1
lci-seq-closed = refl

-- a delay by one unit is two half-unit delays

lci-tick : Grade.ι G (# 1) ≡ Grade.ι G (1 / 2) L.·ˡ Grade.ι G (1 / 2)
lci-tick = refl

------------------------------------------------------------------------
-- The join is the weaker bound

lci-join-side : L.> # 1 L.⊔ˡ L.≥ # 1 ≡ L.≥ # 1
lci-join-side = refl

lci-join-point : L.> # 1 L.⊔ˡ L.> # 2 ≡ L.> # 1
lci-join-point = refl

------------------------------------------------------------------------
-- The unit is the greatest grade, so the zero-product law holds of
-- every product

lci-zero-product : L.> # 1 L.·ˡ L.≥ # 2 L.≾ˡ Grade.𝟏 G
lci-zero-product = ≾ˡ!

lci-zero-product-factor : L.> # 1 L.≾ˡ Grade.𝟏 G
lci-zero-product-factor = Grade.≾-zero-productˡ G {L.> # 1} {L.≥ # 2} lci-zero-product

-- the unit is not least: an open bound at zero lies below it, and
-- not above it

lci-not-least : ¬ (Grade.𝟏 G L.≾ˡ L.> # 0)
lci-not-least = ⋠ˡ!

------------------------------------------------------------------------
-- The morphisms into the grade

lci-closed : GradeMorphism.map L.closed→cut Closed.[ 1 / 2 ,+∞⟩ ≡ L.≥ 1 / 2
lci-closed = refl

lci-interval : GradeMorphism.map L.interval→cut T.] # 1 , ↑ # 2 [ ≡ L.> # 1
lci-interval = refl

lci-discrete : GradeMorphism.map L.lower-bound→rational-cut Discrete.[ 3 ,+∞⟩ ≡ L.≥ # 3
lci-discrete = refl
