------------------------------------------------------------------------
-- Worked instances of upper bounds: an upper bound on                --
-- elapsed time.                                                      --
--                                                                    --
-- The mirror image of the lower-bound grade: `[0, m ] ≾ [0, n ]` is  --
-- `m ≤ n`, so the smaller bound is the stronger claim. Weakening     --
-- relaxes a deadline.                                                --
--                                                                    --
-- The `uplink` run of the sensor node (read, idle two ticks, send)   --
-- takes at most 9 ticks under `opTime`.                              --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.UpperBound where

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Time.UpperBound
  using ([0,_]; ℕ∞; ↑_; ∞; upper-bound)
  renaming (𝕀ᵣ to 𝕀ʳ; _·ₒ_ to _·ʳ_; 𝟏ₒ to 𝟏ʳ; _≾ₒ_ to _≾ʳ_; ⊤ₒ to ⊤ʳ)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

uplink-hi : 𝕀ʳ
uplink-hi = [0, ↑ 9 ]

upper-weaken : [0, ↑ 9 ] ≾ʳ [0, ↑ 12 ]
upper-weaken = ≤!

upper-no-tighten : ¬ ([0, ↑ 12 ] ≾ʳ [0, ↑ 9 ])
upper-no-tighten = ≰!

upper-seq : [0, ↑ 1 ] ·ʳ [0, ↑ 8 ] ≡ [0, ↑ 9 ]
upper-seq = refl

-- the unit is the least grade: "at most 0 ticks" is the strongest
-- deadline there is

upper-unit : 𝟏ʳ ≡ [0, ↑ 0 ]
upper-unit = refl

upper-unit-bottom : 𝟏ʳ ≾ʳ [0, ↑ 9 ]
upper-unit-bottom = ≤!

-- and the greatest grade is `[0, ∞ ]`, which imposes no deadline; it is
-- absorbing, a run after an unbounded one being unbounded too

upper-top : ⊤ʳ ≡ [0, ∞ ]
upper-top = refl

upper-weaken-to-top : [0, ↑ 9 ] ≾ʳ ⊤ʳ
upper-weaken-to-top = _

upper-top-absorbs : ⊤ʳ ·ʳ [0, ↑ 9 ] ≡ ⊤ʳ
upper-top-absorbs = refl

upper-ι : Grade.ι upper-bound 9 ≡ [0, ↑ 9 ]
upper-ι = refl
