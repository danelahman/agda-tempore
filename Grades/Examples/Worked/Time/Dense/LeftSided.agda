------------------------------------------------------------------------
-- Worked instances of the dense left-sided grade.                    --
--                                                                    --
-- "At least `q` units": orderings between concrete grades, each      --
-- established by the decision procedure of the grade; sequencing and --
-- the join, computed.                                                --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Dense.LeftSided where

open import Relation.Nullary using (¬_)

open import Util.Equality

import Grades.Examples.Time.Dense.LeftSided as L

open import Grades.Examples.Time.Dense.ExtendedRational
  using (_/_; #_; nonZero)

open import Grades.Examples.Worked.Time.Dense.Decide using (module Decide)

open Decide L.dense-left-sided-intervals renaming (≾! to ≾ˡ!; ⋠! to ⋠ˡ!)

------------------------------------------------------------------------
-- Left-sided: "at least q units"
--
-- A larger lower bound is the stronger claim, so it sits below.

-- "at least 1" is stronger than "at least 0.5"

lsi-weaken : L.[ # 1 ,+∞⟩ L.≾ₒ L.[ 1 / 2 ,+∞⟩
lsi-weaken = ≾ˡ!

lsi-no-strengthen : ¬ (L.[ 1 / 2 ,+∞⟩ L.≾ₒ L.[ # 1 ,+∞⟩)
lsi-no-strengthen = ⋠ˡ!

-- two half-unit delays make at least one unit

lsi-halves : L.[ 1 / 2 ,+∞⟩ L.·ₒ L.[ 1 / 2 ,+∞⟩ ≡ L.[ # 1 ,+∞⟩
lsi-halves = refl

-- the join keeps the smaller guarantee

lsi-join : L.[ 1 / 3 ,+∞⟩ L.⊔ₒ L.[ 1 / 2 ,+∞⟩ ≡ L.[ 1 / 3 ,+∞⟩
lsi-join = refl
