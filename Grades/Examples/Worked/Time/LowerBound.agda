------------------------------------------------------------------------
-- Worked instances of lower bounds: a lower bound on elapsed         --
-- time.                                                              --
--                                                                    --
-- `[ m ,+∞⟩ ≾ [ n ,+∞⟩` is `n ≤ m`: a larger lower bound is the      --
-- stronger claim and lies below. Weakening decreases the amount of   --
-- time known to have passed.                                         --
--                                                                    --
-- The `uplink` run of the sensor node (read, idle two ticks, send)   --
-- takes at least 7 ticks under `opTime`.                             --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.LowerBound where

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Time.LowerBound
  using ([_,+∞⟩; lower-bound)
  renaming (𝕀 to 𝕀ˡ; _·ₒ_ to _·ˡ_; 𝟏ₒ to 𝟏ˡ; _≾ₒ_ to _≾ˡ_)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

uplink-lo : 𝕀ˡ
uplink-lo = [ 7 ,+∞⟩

-- "at least 7" is a stronger guarantee than "at least 4", so it is the
-- smaller grade

lower-weaken : [ 7 ,+∞⟩ ≾ˡ [ 4 ,+∞⟩
lower-weaken = ≤!

-- and the other direction fails: nothing lets a grade claim more time
-- has passed than it recorded

lower-no-strengthen : ¬ ([ 4 ,+∞⟩ ≾ˡ [ 7 ,+∞⟩)
lower-no-strengthen = ≰!

-- sequencing adds the guarantees: read (≥1) then the rest of the uplink
-- (≥6) guarantees ≥7

lower-seq : [ 1 ,+∞⟩ ·ˡ [ 6 ,+∞⟩ ≡ [ 7 ,+∞⟩
lower-seq = refl

-- the unit claims nothing, and so is the largest grade

lower-unit : 𝟏ˡ ≡ [ 0 ,+∞⟩
lower-unit = refl

lower-unit-top : [ 7 ,+∞⟩ ≾ˡ 𝟏ˡ
lower-unit-top = ≤!

-- so the unit is the designated greatest grade here, and it is not
-- absorbing

lower-top : Grade.⊤ lower-bound ≡ 𝟏ˡ
lower-top = refl

-- `n` time steps, as a grade

lower-ι : Grade.ι lower-bound 7 ≡ [ 7 ,+∞⟩
lower-ι = refl
