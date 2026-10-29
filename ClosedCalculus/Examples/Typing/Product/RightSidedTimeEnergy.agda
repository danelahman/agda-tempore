------------------------------------------------------------------------
-- Typed example computations at upper bounds on time paired with an  --
-- energy budget.                                                     --
--                                                                    --
-- Effect grades and resource grades are both `([0, n ] , [0, e ])`,  --
-- "at most `n` time steps and at most `e` units of energy", and an   --
-- operation is graded by its worst-case time and the energy it       --
-- draws: read 1 and 1, write 3 and 2, send 6 and 5. Idling spends    --
-- time and draws no energy.                                          --
--                                                                    --
-- As a resource grade, `[ ([0, n ] , [0, e ]) ] A` is a calibration  --
-- that drifts with time and with use: claimable while at most `n`    --
-- steps have passed and at most `e` units have been drawn since      --
-- boxing. The same elapsed time can keep or lose it, according to    --
-- whether it was spent idling or working; both cases are shown       --
-- below.                                                             --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order   --
-- behave as at the upper bounds on time: a reading goes stale after  --
-- any activity, and a handler clause may discard its continuation.   --
--                                                                    --
-- Every claim is checked componentwise, `≤!` on the time and on the  --
-- energy; a refutation names the component that fails.               --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding.                                                   --
------------------------------------------------------------------------

module ClosedCalculus.Examples.Typing.Product.RightSidedTimeEnergy where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)

open import Grades.Examples.Time.RightSided
  using (𝕀ᵣ; ↑_; uₒ-least)
  renaming ([0,_] to ⌈0,_⌉)
open import Grades.Examples.Product.RightSidedTimeEnergy
  using (right-sided-time×energy)

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; slow)
open import Grades.Examples.Worked.Operations.Footprint using (draws)

open import Grades.Examples.Worked.Time.Decide using (≤!; ≰!)

-- every bound written below is finite

[0,_] : ℕ → 𝕀ᵣ
[0, n ] = ⌈0, ↑ n ⌉

------------------------------------------------------------------------
-- The operations, graded by worst-case time and the energy drawn

opTime : Op → 𝕀ᵣ × 𝕀ᵣ
opTime o = ([0, slow o ] , [0, draws o ])

open import ClosedCalculus.Examples.Typing.Core
  right-sided-time×energy opTime

------------------------------------------------------------------------
-- Effectful computations

sampling : [] ⊢C⦂ Reading ‼ ([0, 1 ] , [0, 1 ])
sampling =
  perform read ⋆                     -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
    (return here)

relaying : [] ⊢C⦂ Unit ‼ ([0, 7 ] , [0, 6 ])
relaying =
  perform read ⋆                     -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
    (perform send here               -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ Unit
      (return ⋆))

-- idling spends time and no energy

idling : [] ⊢C⦂ Unit ‼ ([0, 5 ] , [0, 0 ])
idling = delay 5 (return ⋆)          -- ⟨ ([0, 5 ] , [0, 0 ]) ⟩

-- and a reading goes stale under it all the same, on the time
-- component

reading-stale-after-idling : ¬ (uᵣ ·ᵣ of-durʳ 1 ≾ᵣ uᵣ)
reading-stale-after-idling (late , _) = ≰! late

------------------------------------------------------------------------
-- An energy budget
--
-- Thirty steps and twelve units.

budget : E
budget = ([0, 30 ] , [0, 12 ])

-- two uplinks, spaced by ten ticks of idling, fit it: the idling costs
-- time the budget has to spare, and no energy

spaced-uplinks : [] ⊢C⦂ Unit ‼ budget
spaced-uplinks =
  coerce (≤! , ≤!)
    (perform read ⋆                  -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
      (perform send here             -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ Unit
        (delay 10                    -- ⟨ ([0, 10 ] , [0, 0 ]) ⟩
          (perform read ⋆            -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
            (perform send here       -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ Unit
              (return ⋆))))))

-- three uplinks back to back take less time than that and draw more
-- energy than the budget holds

three-uplinks-overdraw : ¬ (([0, 21 ] , [0, 18 ]) ≾ₑ budget)
three-uplinks-overdraw (_ , overdrawn) = ≰! overdrawn

------------------------------------------------------------------------
-- Conditional branching
--
-- The join is taken componentwise, so a conditional is charged its
-- slower branch's time and its hungrier branch's energy, even when no
-- single branch spends both.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ([0, 8 ] , [0, 5 ])
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce (≤! , ≤!) (perform send here (return ⋆))
    `else coerce (≤! , ≤!) (delay 8 (return ⋆))

------------------------------------------------------------------------
-- Unboxing: a calibration that drifts
--
-- Valid for ten steps and six units of energy.

calibration : R
calibration = ([0, 10 ] , [0, 6 ])

-- claimed after eight ticks of idling: eight steps, nothing drawn

claim-after-idling : [] ⊢C⦂ Unit ‼ ([0, 14 ] , [0, 5 ])
claim-after-idling =
  box calibration (const 42)         -- ∷ [ calibration ] Reading
    (delay 8                         -- ⟨ ([0, 8 ] , [0, 0 ]) ⟩
      (unbox (Tl-⟨⟩ Hd) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
        (perform send here (return ⋆))))

-- claimed after an uplink: seven steps, and the six units exactly

claim-after-relaying : [] ⊢C⦂ Unit ‼ ([0, 10 ] , [0, 8 ])
claim-after-relaying =
  box calibration (const 42)         -- ∷ [ calibration ] Reading
    (perform read ⋆                  -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
      (perform send here             -- ⟨ ([0, 6 ] , [0, 5 ]) ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (≤! , ≤!) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform write here (return ⋆)))))

-- eight steps spent working instead of idling -- two readings and a
-- transmission -- draw seven units, and the claim is refused

drained : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ calibration)
drained (_ , overdrawn) = ≰! overdrawn

-- and idling past ten steps drifts it, having drawn nothing

drifted : ¬ (uᵣ ·ᵣ of-durʳ 11 ≾ᵣ calibration)
drifted (late , _) = ≰! late

------------------------------------------------------------------------
-- Effect handling

forwarded : [] ⊢C⦂ Reading ‼ ([0, 1 ] , [0, 1 ])
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ ([0, 1 ] , [0, 1 ]) ⟩ ∷ Reading
      (return here)

-- a clause may drop its continuation: doing nothing meets every
-- deadline and every budget

nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits op ε'' =
  uₒ-least (proj₁ (op-grade op ·ₑ ε'')) , uₒ-least (proj₂ (op-grade op ·ₑ ε''))

-- the barrier `⊤ᵣ` has no deadline, so no clause may close over a
-- reading

reading-stale-at-⊤ : ¬ (uᵣ ·ᵣ ⊤ᵣ ≾ᵣ uᵣ)
reading-stale-at-⊤ (() , _)

no-reporting : (op : Op) → (ε'' : E)
             → ¬ (uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ uᵣ)
no-reporting op ε'' bound =
  reading-stale-at-⊤
    (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ} {op-grade op}
      (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op} {ε''} bound))
