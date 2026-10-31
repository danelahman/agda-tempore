------------------------------------------------------------------------
-- Worked instances of right-sided intervals: an upper bound on       --
-- elapsed time.                                                      --
--                                                                    --
-- The mirror image of the left-sided grade: `[0, m ] ≾ [0, n ]` is   --
-- `m ≤ n`, so the smaller bound is the stronger claim. Weakening     --
-- relaxes a budget.                                                  --
--                                                                    --
-- The `uplink` run of the sensor node (read, idle two ticks, send)   --
-- takes at most 9 ticks under `opTime`.                              --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.RightSided where

open import Relation.Nullary using (¬_)

open import Grades.Base using (Grade)

open import Util.Equality

open import Grades.Examples.Time.RightSided
  using ([0,_]; ℕ∞; ↑_; ∞; right-sided-intervals)
  renaming (𝕀ᵣ to 𝕀ʳ; _·ₒ_ to _·ʳ_; uₒ to uʳ; _≾ₒ_ to _≾ʳ_; ⊤ₒ to ⊤ʳ)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

uplink-hi : 𝕀ʳ
uplink-hi = [0, ↑ 9 ]

rsi-weaken : [0, ↑ 9 ] ≾ʳ [0, ↑ 12 ]
rsi-weaken = ≤!

rsi-no-tighten : ¬ ([0, ↑ 12 ] ≾ʳ [0, ↑ 9 ])
rsi-no-tighten = ≰!

rsi-seq : [0, ↑ 1 ] ·ʳ [0, ↑ 8 ] ≡ [0, ↑ 9 ]
rsi-seq = refl

-- the unit is the least grade: "at most 0 ticks" is the strongest
-- budget there is

rsi-unit : uʳ ≡ [0, ↑ 0 ]
rsi-unit = refl

rsi-unit-bottom : uʳ ≾ʳ [0, ↑ 9 ]
rsi-unit-bottom = ≤!

-- and the greatest grade is `[0, ∞ ]`, which imposes no deadline; it is
-- absorbing, a run after an unbounded one being unbounded too

rsi-top : ⊤ʳ ≡ [0, ∞ ]
rsi-top = refl

rsi-weaken-to-top : [0, ↑ 9 ] ≾ʳ ⊤ʳ
rsi-weaken-to-top = _

rsi-top-absorbs : ⊤ʳ ·ʳ [0, ↑ 9 ] ≡ ⊤ʳ
rsi-top-absorbs = refl

rsi-of-dur : Grade.of-dur right-sided-intervals 9 ≡ [0, ↑ 9 ]
rsi-of-dur = refl
