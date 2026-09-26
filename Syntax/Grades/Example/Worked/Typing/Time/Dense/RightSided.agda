------------------------------------------------------------------------
-- Typed example computations at upper bounds on dense time.          --
--                                                                    --
-- Effect grades and resource grades are both `[0, q ]`, "at most `q` --
-- units", with `q` a non-negative rational. The clock of the node    --
-- counts whole ticks, and the figures of the alphabet (read 1, write --
-- 3, send 6 at worst) are rounded up to whole ticks. In dense time   --
-- the operations take at most read 1/2, write 5/2 and send 11/2,     --
-- each half a tick below its rounded figure; `delay` idles whole     --
-- ticks.                                                             --
--                                                                    --
-- The grade behaves as the discrete upper bounds do: `[ ρ ] A` is a  --
-- lease that expires, a reading goes stale after any activity, and a --
-- handler clause may discard its continuation. The rationals add     --
-- precision: a lease can be spent in half ticks, and a claim that    --
-- the rounded figures refuse can hold at the measured ones. Both     --
-- cases are shown below.                                             --
--                                                                    --
-- Every claim is checked by deciding `≤` on the rationals, `≤ᵈ!` and --
-- `≰ᵈ!`.                                                             --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding.                                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Time.Dense.RightSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Time.Dense.RightSided
  using (𝕀ᵣ; ↑_; ℚ≥0; _/_; #_; nonZero; uₒ-least;
         dense-right-sided-intervals; right-sided→dense)
  renaming ([0,_] to ⌈0,_⌉; _≤_ to _≤ᵈ_; _≤?_ to _≤ᵈ?_)

import Syntax.Grades.Example.Time.RightSided as Discrete

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send; slow)

-- every deadline written below is finite

[0,_] : ℚ≥0 → 𝕀ᵣ
[0, q ] = ⌈0, ↑ q ⌉

-- comparisons of rationals, decided

≤ᵈ! : {p q : ℚ≥0} {w : True (p ≤ᵈ? q)} → p ≤ᵈ q
≤ᵈ! {w = w} = toWitness w

≰ᵈ! : {p q : ℚ≥0} {w : False (p ≤ᵈ? q)} → ¬ (p ≤ᵈ q)
≰ᵈ! {w = w} = toWitnessFalse w

------------------------------------------------------------------------
-- The operations, graded by their measured worst case

opTime : Op → 𝕀ᵣ
opTime read  = [0, 1 / 2 ]
opTime write = [0, 5 / 2 ]
opTime send  = [0, 11 / 2 ]

-- the whole-tick figures of the alphabet, read in dense time through
-- the embedding of the discrete intervals

ticks : Op → 𝕀ᵣ
ticks o = _→ᵍ_.map right-sided→dense Discrete.[0, Discrete.↑ slow o ]

open import Syntax.Grades.Example.Worked.Typing.Core
  dense-right-sided-intervals opTime
  hiding (_/_)

-- each measured figure is within its rounded one

measured-within-ticks : (o : Op) → opTime o ≾ₑ ticks o
measured-within-ticks read  = ≤ᵈ!
measured-within-ticks write = ≤ᵈ!
measured-within-ticks send  = ≤ᵈ!

------------------------------------------------------------------------
-- Effectful computations

sampling : [] ⊢C⦂ Reading ‼ [0, 1 / 2 ]
sampling =
  perform read ⋆                     -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ [0, # 3 ]
storing =
  perform read ⋆                     -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
    (perform write here              -- ⟨ [0, 5 / 2 ] ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ [0, # 6 ]
relaying =
  perform read ⋆                     -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
    (perform send here               -- ⟨ [0, 11 / 2 ] ⟩ ∷ Unit
      (return ⋆))

-- half a unit is enough for a reading to go stale

reading-stale-after-sampling : ¬ (uᵣ ·ᵣ opTime read ≾ᵣ uᵣ)
reading-stale-after-sampling = ≰ᵈ!

------------------------------------------------------------------------
-- Sub-effecting
--
-- A deadline may be relaxed by any rational amount, and never
-- tightened.

relaxing-a-deadline : [] ⊢C⦂ Unit ‼ [0, 13 / 2 ]
relaxing-a-deadline =
  coerce ≤ᵈ! (perform read ⋆ (perform send here (return ⋆)))

tightening-a-deadline :
  ¬ (opTime read ·ₑ (opTime send ·ₑ uₑ) ≾ₑ [0, 23 / 4 ])
tightening-a-deadline = ≰ᵈ!

------------------------------------------------------------------------
-- Conditional branching
--
-- The storing branch is coerced to the transmitting branch's deadline.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ [0, 11 / 2 ]
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then perform send here (return ⋆)
    `else coerce ≤ᵈ! (perform write here (return ⋆))

------------------------------------------------------------------------
-- Unboxing: a lease measured precisely
--
-- A lease of six units, claimed after a reading and a transmission:
-- measured, they take exactly the six.

claim-after-relaying : [] ⊢C⦂ Unit ‼ [0, 23 / 2 ]
claim-after-relaying =
  box {ρ = [0, # 6 ]} (const 42)     -- ∷ [ [0, # 6 ] ] Reading
    (perform read ⋆                  -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
      (perform send here             -- ⟨ [0, 11 / 2 ] ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) ≤ᵈ! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

-- charged their whole-tick figures, the same two operations take seven,
-- and the claim is refused

rounded-up-it-expires :
  ¬ (uᵣ ·ᵣ ticks read ·ᵣ ticks send ≾ᵣ [0, # 6 ])
rounded-up-it-expires = ≰ᵈ!

-- A lease of three and a half units: idling covers whole ticks of it,
-- and the half tick left over is exactly a reading.

half-tick-lease : R
half-tick-lease = [0, 7 / 2 ]

claim-after-idling-and-sampling : [] ⊢C⦂ Unit ‼ [0, # 9 ]
claim-after-idling-and-sampling =
  box {ρ = half-tick-lease} (const 42)
                                     -- ∷ [ [0, 7 / 2 ] ] Reading
    (delay 3                         -- ⟨ [0, # 3 ] ⟩
      (perform read ⋆                -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-⟨⟩ Hd))) ≤ᵈ! (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

-- two readings and a store fill it as well

claim-after-storing-twice : [] ⊢C⦂ Unit ‼ [0, # 9 ]
claim-after-storing-twice =
  box {ρ = half-tick-lease} (const 42)
                                     -- ∷ [ [0, 7 / 2 ] ] Reading
    (perform read ⋆                  -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
      (perform write here            -- ⟨ [0, 5 / 2 ] ⟩ ∷ Unit
        (perform read ⋆              -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
          (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))))) ≤ᵈ!
                 (<:ᵛ-refl _)        -- ∷ Reading
            (perform send here (return ⋆))))))

-- a fourth tick of idling overruns it by half a unit

idling-overruns : ¬ (uᵣ ·ᵣ of-natʳ 4 ≾ᵣ half-tick-lease)
idling-overruns = ≰ᵈ!

-- and so does a second reading after the idling

sampling-twice-overruns :
  ¬ (uᵣ ·ᵣ of-natʳ 3 ·ᵣ opTime read ·ᵣ opTime read ≾ᵣ half-tick-lease)
sampling-twice-overruns = ≰ᵈ!

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ [0, 1 / 2 ]
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ [0, 1 / 2 ] ⟩ ∷ Reading
      (return here)

-- a clause may drop its continuation: returning at once meets every
-- deadline

nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits op ε'' = uₒ-least (op-grade op ·ₑ ε'')

suppressed : [] ⊢C⦂ Unit ‼ [0, # 3 ]
suppressed =
  handle perform read ⋆ (perform write here (return ⋆))
    `with discarding {[]} nothing-fits
    `in                              -- ⟨ [0, # 3 ] ⟩ ∷ Unit
      (return ⋆)

-- the barrier `⊤ᵣ` is `[0, ∞ ]`, so no clause may close over a reading

reading-stale-at-⊤ : ¬ (uᵣ ·ᵣ ⊤ᵣ ≾ᵣ uᵣ)
reading-stale-at-⊤ ()

no-reporting : (op : Op) → (ε'' : E)
             → ¬ (uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ uᵣ)
no-reporting op ε'' bound =
  reading-stale-at-⊤
    (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ} {op-grade op}
      (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op} {ε''} bound))
