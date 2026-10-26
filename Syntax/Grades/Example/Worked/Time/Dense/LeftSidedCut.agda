------------------------------------------------------------------------
-- Worked instances of the dense left-sided grade with open or closed --
-- ends.                                                              --
--                                                                    --
-- "At least `p` units" and "more than `p` units": orderings between  --
-- concrete grades, each established by the decision procedure of the --
-- grade; sequencing, the join and the morphisms into the grade,      --
-- computed.                                                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Time.Dense.LeftSidedCut where

open import Relation.Nullary using (¬_)

open import Syntax.Grades using (Grade; GradeMorphism)

open import Util.Equality

import Syntax.Grades.Example.Time.Dense.LeftSidedCut as L

import Syntax.Grades.Example.Time.Dense.LeftSided as Closed
import Syntax.Grades.Example.Time.Dense.TwoSided as T
import Syntax.Grades.Example.Time.LeftSided as Discrete

open import Syntax.Grades.Example.Time.Dense.ExtendedRational
  using (↑_; _/_; #_; nonZero)

open import Syntax.Grades.Example.Worked.Time.Dense.Decide using (module Decide)

open Decide L.dense-left-sided-cut-intervals renaming (≾! to ≾ˡ!; ⋠! to ⋠ˡ!)

G = L.dense-left-sided-cut-intervals

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

lci-tick : Grade.of-dur G (# 1) ≡ Grade.of-dur G (1 / 2) L.·ˡ Grade.of-dur G (1 / 2)
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

lci-zero-product : L.> # 1 L.·ˡ L.≥ # 2 L.≾ˡ Grade.u G
lci-zero-product = ≾ˡ!

lci-zero-product-factor : L.> # 1 L.≾ˡ Grade.u G
lci-zero-product-factor = Grade.≾-zero-productˡ G {L.> # 1} {L.≥ # 2} lci-zero-product

-- the unit is not least: an open bound at zero lies below it, and
-- not above it

lci-not-least : ¬ (Grade.u G L.≾ˡ L.> # 0)
lci-not-least = ⋠ˡ!

------------------------------------------------------------------------
-- The morphisms into the grade

lci-closed : GradeMorphism.map L.closed→cut Closed.[ 1 / 2 ,+∞⟩ ≡ L.≥ 1 / 2
lci-closed = refl

lci-two-sided : GradeMorphism.map L.two-sided→cut T.] # 1 , ↑ # 2 [ ≡ L.> # 1
lci-two-sided = refl

lci-discrete : GradeMorphism.map L.left-sided→dense-cut Discrete.[ 3 ,+∞⟩ ≡ L.≥ # 3
lci-discrete = refl
